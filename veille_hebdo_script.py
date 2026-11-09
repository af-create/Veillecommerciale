#!/usr/bin/env python3
"""
Veille B2B hebdomadaire pour courtier en assurances (base : Mérignac)

Sources (gratuites, sans clé API) :
  - BODACC (DILA) : cessions de fonds, modifications (dirigeants, capital...)
  - API Recherche d'entreprises (data.gouv) : CA, effectif, dirigeants, coordonnées
  - Google Actualités (RSS) : DAF, permis de construire, levées de fonds, recrutements...

Usage :
  python veille.py --dry-run   -> génère newsletter.html sans envoyer
  python veille.py             -> génère et envoie par email (variables SMTP_* requises)
  python veille.py --debug     -> affiche un enregistrement BODACC brut (pour vérifier les champs)
"""
import html
import math
import os
import re
import smtplib
import sys
import time
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import parsedate_to_datetime

import requests

# ---------------------------------------------------------------- CONFIG ----
BASE = (44.8283, -0.7156)          # Mérignac
MAX_KM_VOL_OISEAU = 170            # ~2h30 de route ≈ 200 km routiers ≈ 170 km à vol d'oiseau
DEPARTEMENTS = ["33", "24", "40", "47", "17", "16", "64", "32", "82", "79"]
CA_MIN = 5_000_000
CA_MAX = 500_000_000               # au-delà : exclu
JOURS = 7                          # fenêtre de la veille
BODACC_FAMILLES = ["vente", "modification"]   # codes du champ 'familleavis'
KEEP_UNKNOWN_CA = True             # garder si CA non publié mais effectif >= 20 salariés

BODACC_URL = ("https://bodacc-datadila.opendatasoft.com/api/explore/v2.1/"
              "catalog/datasets/annonces-commerciales/records")
SEARCH_URL = "https://recherche-entreprises.api.gouv.fr/search"

# Liste NON exhaustive à maintenir (CAC 40 / SBF 120 / grands groupes). Minuscules.
BIG_GROUPS = [
    "totalenergies", "lvmh", "l'oréal", "hermès", "sanofi", "schneider electric", "airbus",
    "air liquide", "bnp paribas", "axa", "crédit agricole", "société générale", "danone",
    "essilorluxottica", "kering", "orange", "pernod ricard", "publicis", "renault", "safran",
    "saint-gobain", "stellantis", "thales", "veolia", "vinci", "carrefour", "michelin",
    "stmicroelectronics", "teleperformance", "legrand", "dassault systèmes", "capgemini",
    "accor", "bouygues", "edenred", "engie", "eurofins", "getlink", "eiffage", "colas",
    "eurovia", "spie", "atos", "sodexo", "alstom", "arkema", "bureau veritas", "covivio",
    "gecina", "klépierre", "unibail", "valeo", "forvia", "faurecia", "ubisoft", "vallourec",
    "auchan", "leclerc", "intermarché", "casino", "système u", "decathlon", "leroy merlin",
    "castorama", "fnac darty", "lactalis", "groupe la poste", "sncf", "edf", "enedis",
    "bolloré", "fayat", "ramsay", "korian", "clariane", "elior", "derichebourg", "randstad",
    "adecco", "manpower", "dalkia", "idex", "suez", "nexity", "cegelec", "ceva", "geodis",
]

PRESS_QUERIES = [
    '"nouveau DAF" OR "nouveau directeur financier" Gironde OR Bordeaux',
    "permis de construire entrepôt OR usine OR siège Bordeaux OR Gironde",
    "levée de fonds Bordeaux OR Nouvelle-Aquitaine entreprise",
    "recrute OR recrutement entreprise industrielle Gironde",
    "rachat OR acquisition entreprise Gironde OR Bordeaux",
    "ouverture filiale export entreprise Bordeaux OR Aquitaine",
    "investissement extension site production Gironde OR Landes OR Dordogne",
]

EFFECTIFS = {"11": "10-19", "12": "20-49", "21": "50-99", "22": "100-199", "31": "200-249",
             "32": "250-499", "41": "500-999", "42": "1000-1999", "51": "2000-4999",
             "52": "5000-9999", "53": "10000+"}
EFFECTIF_OK_SI_CA_INCONNU = {"12", "21", "22", "31", "32", "41", "42", "51", "52", "53"}

SIGNALS = {
    "vente": ("Cession / vente de fonds", "high",
              "Moment clé : transfert ou résiliation des polices, garantie de passif, "
              "RC et multirisque du repreneur. Contacter cédant ET repreneur."),
    "modification": ("Modification (dirigeant, capital, siège...)", "medium",
                     "Changement de dirigeant ou de structure : bon prétexte pour proposer "
                     "un audit gratuit des contrats (RC dirigeants, homme-clé, multirisque)."),
}


# ---------------------------------------------------------------- UTILS -----
def haversine(lat1, lon1, lat2, lon2):
    r = 6371
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dphi, dl = p2 - p1, math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def siren_of(rec):
    reg = rec.get("registre")
    if isinstance(reg, list):
        reg = reg[-1] if reg else ""
    digits = "".join(c for c in str(reg or "") if c.isdigit())
    return digits[:9] if len(digits) >= 9 else None


def get_json(url, params, retries=2):
    for i in range(retries + 1):
        r = requests.get(url, params=params, timeout=30,
                         headers={"User-Agent": "veille-courtage/1.0"})
        if r.status_code == 429 and i < retries:
            time.sleep(2 * (i + 1))
            continue
        r.raise_for_status()
        return r.json()


# ---------------------------------------------------------------- BODACC ----
def bodacc_fetch(since):
    deps = ",".join(f'"{d}"' for d in DEPARTEMENTS)
    fams = ",".join(f'"{f}"' for f in BODACC_FAMILLES)
    where = (f"dateparution >= date'{since.isoformat()}' "
             f"AND numerodepartement IN ({deps}) AND familleavis IN ({fams})")
    out, offset = [], 0
    while offset < 3000:
        data = get_json(BODACC_URL, {"where": where, "limit": 100, "offset": offset,
                                     "order_by": "dateparution desc"})
        res = data.get("results", [])
        out += res
        if len(res) < 100:
            break
        offset += 100
    return out


# ------------------------------------------------------------ ENRICHISSEMENT -
_cache = {}


def enrich(siren):
    if siren in _cache:
        return _cache[siren]
    try:
        data = get_json(SEARCH_URL, {"q": siren, "per_page": 1})
        res = data.get("results", [])
        e = res[0] if res and res[0].get("siren") == siren else None
    except Exception as exc:
        print(f"  ! enrichissement {siren} : {exc}")
        e = None
    _cache[siren] = e
    time.sleep(0.2)   # reste sous la limite de débit de l'API
    return e


def latest_ca(e):
    fin = e.get("finances") or {}
    if not fin:
        return None
    return fin[max(fin)].get("ca")


def big_group_reason(e):
    if e.get("categorie_entreprise") == "GE":
        return "Grande entreprise (catégorie INSEE)"
    names = [e.get("nom_complet") or ""]
    for d in e.get("dirigeants") or []:
        if d.get("type_dirigeant") == "personne morale":
            names.append(d.get("denomination") or "")
    blob = " ".join(names).lower()
    for g in BIG_GROUPS:
        if re.search(r"(?<!\w)" + re.escape(g) + r"(?!\w)", blob):
            return f"Lié à {g}"
    return None


def build_opportunities():
    since = date.today() - timedelta(days=JOURS)
    records = bodacc_fetch(since)
    print(f"BODACC : {len(records)} annonces depuis le {since}")

    by_siren = {}
    for rec in records:
        s = siren_of(rec)
        if s:
            by_siren.setdefault(s, []).append(rec)
    print(f"{len(by_siren)} entreprises distinctes à qualifier...")

    stats = {"hors_ca": 0, "groupe": 0, "distance": 0, "ca_inconnu_ecarte": 0}
    opps = []
    for siren, recs in by_siren.items():
        e = enrich(siren)
        if not e:
            continue

        ca = latest_ca(e)
        eff = (e.get("tranche_effectif_salarie") or "")
        if ca is not None:
            if ca < CA_MIN or ca > CA_MAX:
                stats["hors_ca"] += 1
                continue
        else:
            if not (KEEP_UNKNOWN_CA and eff in EFFECTIF_OK_SI_CA_INCONNU):
                stats["ca_inconnu_ecarte"] += 1
                continue

        reason = big_group_reason(e)
        if reason:
            stats["groupe"] += 1
            continue

        siege = e.get("siege") or {}
        try:
            km = haversine(BASE[0], BASE[1], float(siege["latitude"]), float(siege["longitude"]))
            if km > MAX_KM_VOL_OISEAU:
                stats["distance"] += 1
                continue
        except (KeyError, TypeError, ValueError):
            km = None

        fam = "vente" if any(r.get("familleavis") == "vente" for r in recs) else "modification"
        label, prio, approach = SIGNALS[fam]
        opps.append({
            "siren": siren,
            "nom": e.get("nom_complet") or recs[0].get("commercant") or siren,
            "ville": siege.get("libelle_commune") or recs[0].get("ville") or "",
            "km": km, "ca": ca, "ca_annee": max(e["finances"]) if e.get("finances") else None,
            "effectif": EFFECTIFS.get(eff, "n.c."),
            "signal": label, "priorite": prio, "approche": approach,
            "date": recs[0].get("dateparution", ""),
            "lien": recs[0].get("url_complete") or "",
            "nb_annonces": len(recs),
        })
    print("Écartés :", stats)
    order = {"high": 0, "medium": 1}
    opps.sort(key=lambda o: (order.get(o["priorite"], 2), o["km"] if o["km"] is not None else 999))
    return opps


# ----------------------------------------------------------------- PRESSE ---
def fetch_press():
    items, seen = [], set()
    limit = datetime.now().astimezone() - timedelta(days=JOURS)
    for q in PRESS_QUERIES:
        try:
            r = requests.get("https://news.google.com/rss/search",
                             params={"q": q + f" when:{JOURS}d", "hl": "fr", "gl": "FR",
                                     "ceid": "FR:fr"}, timeout=30,
                             headers={"User-Agent": "veille-courtage/1.0"})
            r.raise_for_status()
            root = ET.fromstring(r.content)
        except Exception as exc:
            print(f"  ! RSS '{q[:30]}...' : {exc}")
            continue
        for it in root.iter("item"):
            title = (it.findtext("title") or "").strip()
            link = (it.findtext("link") or "").strip()
            if not title or title in seen:
                continue
            try:
                d = parsedate_to_datetime(it.findtext("pubDate"))
                if d < limit:
                    continue
            except Exception:
                d = None
            seen.add(title)
            items.append({"titre": title, "lien": link, "requete": q,
                          "source": it.findtext("source") or "",
                          "date": d.strftime("%d/%m/%Y") if d else ""})
            if sum(1 for i in items if i["requete"] == q) >= 5:
                break
    return items


# ------------------------------------------------------------------- HTML ---
def e(x):
    return html.escape(str(x))


def fmt_ca(ca, annee):
    return "CA non publié" if ca is None else f"CA {ca / 1e6:.1f} M€ ({annee})"


def render(opps, press):
    badge = {"high": ("#fee2e2", "#991b1b", "Priorité haute"),
             "medium": ("#fed7aa", "#9a3412", "Priorité moyenne")}
    cards = ""
    for o in opps:
        bg, fg, lab = badge.get(o["priorite"], badge["medium"])
        dist = f"{o['km']:.0f} km" if o["km"] is not None else "distance n.c."
        d = o["date"]
        try:
            d = datetime.strptime(d, "%Y-%m-%d").strftime("%d/%m/%Y")
        except ValueError:
            pass
        cards += f"""
        <div style="border:1px solid #e5e7eb;border-radius:10px;padding:16px;margin:0 0 14px">
          <span style="background:{bg};color:{fg};font-size:11px;font-weight:700;padding:3px 10px;border-radius:10px">{lab}</span>
          <h3 style="margin:8px 0 2px;font-size:17px;color:#111827">{e(o['nom'])}</h3>
          <div style="font-size:13px;color:#6b7280">{e(o['ville'])} ({dist}) · {e(fmt_ca(o['ca'], o['ca_annee']))} · effectif {e(o['effectif'])} · publié le {e(d)}</div>
          <p style="margin:10px 0 6px;font-size:14px;color:#374151"><b>Signal :</b> {e(o['signal'])}</p>
          <p style="margin:0 0 8px;font-size:13px;color:#047857;background:#ecfdf5;padding:8px;border-radius:6px"><b>Angle d'approche :</b> {e(o['approche'])}</p>
          <a href="https://www.pappers.fr/entreprise/{e(o['siren'])}" style="font-size:12px;color:#4f46e5">Fiche Pappers</a>
          {f' · <a href="{e(o["lien"])}" style="font-size:12px;color:#4f46e5">Annonce BODACC</a>' if o['lien'] else ''}
        </div>"""
    if not cards:
        cards = "<p style='color:#6b7280'>Aucun signal BODACC qualifié cette semaine.</p>"

    press_html = ""
    for p in press:
        press_html += (f"<li style='margin-bottom:8px;font-size:14px'>"
                       f"<a href='{e(p['lien'])}' style='color:#111827'>{e(p['titre'])}</a>"
                       f"<br><span style='font-size:12px;color:#6b7280'>{e(p['date'])}</span></li>")
    if not press_html:
        press_html = "<li style='color:#6b7280'>Rien de notable.</li>"

    today = date.today().strftime("%d/%m/%Y")
    return f"""<!DOCTYPE html><html lang="fr"><body style="margin:0;background:#f5f7fa;font-family:Arial,sans-serif">
    <div style="max-width:680px;margin:0 auto;background:#fff">
      <div style="background:#4f46e5;color:#fff;padding:28px 24px">
        <h1 style="margin:0;font-size:22px">Veille stratégique hebdomadaire</h1>
        <p style="margin:6px 0 0;font-size:14px;opacity:.9">Semaine au {today} · {len(opps)} signaux entreprises · rayon {MAX_KM_VOL_OISEAU} km autour de Mérignac · CA {CA_MIN/1e6:.0f}–{CA_MAX/1e6:.0f} M€</p>
      </div>
      <div style="padding:24px">
        <h2 style="font-size:18px;color:#111827">Signaux légaux qualifiés (BODACC)</h2>{cards}
        <h2 style="font-size:18px;color:#111827;margin-top:28px">Actualités à qualifier (DAF, permis, levées, recrutements...)</h2>
        <p style="font-size:12px;color:#6b7280">Résultats de presse bruts : CA et appartenance à un groupe non vérifiés.</p>
        <ul style="padding-left:18px">{press_html}</ul>
      </div>
      <div style="background:#1f2937;color:#9ca3af;padding:16px 24px;font-size:11px">
        Sources : BODACC (DILA, Licence Ouverte), API Recherche d'entreprises, Google Actualités.
      </div>
    </div></body></html>"""


# ------------------------------------------------------------------ EMAIL ---
def send(body_html, subject):
    host, port = os.environ["SMTP_HOST"], int(os.environ.get("SMTP_PORT", "587"))
    user, pwd = os.environ["SMTP_USER"], os.environ["SMTP_PASSWORD"]
    sender = os.environ.get("MAIL_FROM", user)
    to = [a.strip() for a in os.environ["MAIL_TO"].split(",") if a.strip()]
    msg = MIMEMultipart("alternative")
    msg["Subject"], msg["From"], msg["To"] = subject, sender, ", ".join(to)
    msg.attach(MIMEText("Ouvrez cet email dans un client compatible HTML.", "plain", "utf-8"))
    msg.attach(MIMEText(body_html, "html", "utf-8"))
    with smtplib.SMTP(host, port, timeout=30) as s:
        s.starttls()
        s.login(user, pwd)
        s.sendmail(sender, to, msg.as_string())
    print(f"Newsletter envoyée à {', '.join(to)}")


def main():
    if "--debug" in sys.argv:
        recs = bodacc_fetch(date.today() - timedelta(days=3))
        print(f"{len(recs)} annonces. Premier enregistrement :")
        print(recs[0] if recs else "aucun")
        return
    opps = build_opportunities()
    press = fetch_press()
    body = render(opps, press)
    subject = f"Veille B2B – semaine du {date.today().strftime('%d/%m/%Y')} ({len(opps)} signaux)"
    if "--dry-run" in sys.argv:
        with open("newsletter.html", "w", encoding="utf-8") as f:
            f.write(body)
        print("newsletter.html généré (aucun envoi).")
    else:
        send(body, subject)


if __name__ == "__main__":
    main()
