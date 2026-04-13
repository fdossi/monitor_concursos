#!/usr/bin/env python3
"""
Monitor de Concursos Docentes
Monitora sites de universidades e institutos federais em busca de vagas para docentes.
"""

import sys
import re
import unicodedata
from datetime import datetime, timezone, timedelta
from concurrent.futures import ThreadPoolExecutor, as_completed
from html import escape
from urllib.parse import urljoin, urlparse

import requests
import urllib3
from bs4 import BeautifulSoup

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ──────────────────────────────────────────────
# CONFIGURAÇÕES
# ──────────────────────────────────────────────

TZ_BRASILIA = timezone(timedelta(hours=-3))
REQUEST_TIMEOUT = 20
MAX_WORKERS = 8
MAX_SUBPAGES = 5

# Palavras-chave gerais (todos os sites)
KEYWORDS_GENERAL = [
    "edital de concurso",
    "concurso docente",
    "professor universitario",
    "professor visitante",
    "professor efetivo",
    "professor adjunto",
    "professor auxiliar",
    "professor titular",
    "professor substituto",
    "professor temporario",
    "processo seletivo docente",
    "processo seletivo simplificado",
    "selecao simplificada",
    "selecao de docentes",
    "vaga para docente",
    "concurso publico docente",
    "docente efetivo",
    "docente substituto",
    "contratacao de professor",
    "concurso para professor",
    "edital docente",
    "edital de selecao",
    "abertura de inscricoes",
    "inscricoes abertas",
]

# Palavras-chave adicionais para Institutos Federais (Biologia)
KEYWORDS_IF_BIOLOGY = [
    "professor de biologia",
    "docente de biologia",
    "biologia",
    "ciencias biologicas",
]

# Padrão para identificar Institutos Federais pelo domínio
IF_PATTERN = re.compile(
    r"(?:^|\.)(?:if[a-z-]+\.edu\.br|cefet[a-z-]*(?:\.edu)?\.br)$",
    re.IGNORECASE,
)

# Headers HTTP para evitar bloqueios simples
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "pt-BR,pt;q=0.9,en;q=0.8",
    "Accept-Encoding": "gzip, deflate, br",
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
}

# Palavras em links/âncoras que indicam páginas relevantes
LINK_TRIGGERS = [
    "concurso", "edital", "selecao", "docente", "professor",
    "processo-seletivo", "vaga", "servidor", "rh",
    "gestao-de-pessoas", "servidores",
]

# Extensões a ignorar nos links
SKIP_EXTENSIONS = {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".jpg",
                   ".jpeg", ".png", ".gif", ".zip", ".rar", ".mp4"}

# CSS do relatório (string literal – sem f-string para evitar escape de chaves)
_CSS = """
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
  html { font-size: 16px; scroll-behavior: smooth; }
  body { font-family: "Segoe UI", system-ui, -apple-system, sans-serif;
         background: #f0f2f5; color: #1a1a2e; line-height: 1.6; }
  a { color: #2563eb; text-decoration: none; }
  a:hover { text-decoration: underline; }

  /* Header */
  header { background: linear-gradient(135deg,#1a1a2e 0%,#16213e 55%,#0f3460 100%);
           color:#fff; padding:2.5rem 1.5rem 2rem; text-align:center;
           box-shadow:0 4px 20px rgba(0,0,0,.35); }
  header h1 { font-size:clamp(1.3rem,4vw,2.1rem); font-weight:800;
              letter-spacing:.4px; margin-bottom:.4rem; }
  .subtitle { opacity:.78; font-size:.88rem; }
  .update-time { display:inline-block; margin-top:.85rem;
                 background:rgba(255,255,255,.13); border-radius:20px;
                 padding:.3rem 1rem; font-size:.8rem; }

  /* Stats */
  .stats { display:flex; flex-wrap:wrap; justify-content:center;
           gap:1rem; padding:1.5rem 1rem; max-width:860px; margin:0 auto; }
  .stat { background:#fff; border-radius:12px; padding:.9rem 1.4rem;
          text-align:center; min-width:120px; flex:1;
          box-shadow:0 2px 8px rgba(0,0,0,.07); }
  .stat-num { font-size:2rem; font-weight:800; }
  .num-green { color:#16a34a; }
  .num-blue  { color:#2563eb; }
  .num-red   { color:#dc2626; }
  .stat-label { font-size:.72rem; color:#6b7280; text-transform:uppercase;
                letter-spacing:.5px; margin-top:.1rem; }

  /* Main */
  main { max-width:1100px; margin:0 auto; padding:1rem 1rem 3rem; }
  section, details { margin-bottom:1.6rem; }
  h2 { font-size:.95rem; font-weight:700; margin-bottom:.75rem;
       display:flex; align-items:center; gap:.5rem; color:#374151; }
  .section-count { background:#e5e7eb; border-radius:20px;
                   padding:.1rem .55rem; font-size:.75rem;
                   font-weight:600; color:#374151; }
  details > summary { cursor:pointer; list-style:none; }
  details > summary::-webkit-details-marker { display:none; }
  details > summary h2 { padding:.4rem 0; }
  details[open] > summary h2 { margin-bottom:.75rem; }

  /* Dots */
  .dot { display:inline-block; width:10px; height:10px;
         border-radius:50%; flex-shrink:0; }
  .dot-green { background:#16a34a; }
  .dot-gray  { background:#9ca3af; }
  .dot-red   { background:#dc2626; }

  /* Grid */
  .grid { display:grid; grid-template-columns:repeat(auto-fill,minmax(300px,1fr));
          gap:.9rem; }

  /* Cards */
  .card { background:#fff; border-radius:10px; padding:1rem 1.1rem;
          box-shadow:0 1px 5px rgba(0,0,0,.07); border-left:4px solid #9ca3af;
          transition:box-shadow .2s; }
  .card:hover { box-shadow:0 4px 16px rgba(0,0,0,.13); }
  .c-found { border-left-color:#16a34a; }
  .c-error { border-left-color:#dc2626; }
  .c-none  { border-left-color:#d1d5db; }
  .card-top { display:flex; justify-content:space-between;
              align-items:flex-start; gap:.5rem; margin-bottom:.4rem; }
  .site-url { font-weight:600; font-size:.9rem; color:#1d4ed8;
              word-break:break-all; }
  .pill { background:#dcfce7; color:#166534; border-radius:20px;
          padding:.15rem .65rem; font-size:.72rem; font-weight:700;
          white-space:nowrap; flex-shrink:0; }
  .badge-if { display:inline-block; background:#eff6ff; color:#1d4ed8;
              border:1px solid #bfdbfe; border-radius:4px; font-size:.65rem;
              padding:.1rem .4rem; margin-left:.4rem; font-weight:600;
              vertical-align:middle; }

  /* Page list */
  ul { list-style:none; margin-top:.6rem; display:flex;
       flex-direction:column; gap:.5rem; }
  li { font-size:.8rem; }
  li a { color:#4b5563; word-break:break-all; }
  li a:hover { color:#1d4ed8; }
  .tags { display:flex; flex-wrap:wrap; gap:.25rem; margin-top:.3rem; }
  .tag { background:#f3f4f6; color:#374151; border-radius:4px;
         padding:.1rem .4rem; font-size:.65rem; }
  .errmsg { font-size:.78rem; color:#dc2626; margin-top:.5rem;
            word-break:break-all; }

  /* Footer */
  footer { text-align:center; padding:2rem; font-size:.78rem; color:#9ca3af; }
  footer a { color:#6b7280; }

  @media (max-width:520px) {
    .grid { grid-template-columns:1fr; }
    .stats { flex-direction:column; align-items:stretch; }
  }
"""


# ──────────────────────────────────────────────
# FUNÇÕES AUXILIARES
# ──────────────────────────────────────────────

def normalize(text: str) -> str:
    """Remove acentos e converte para minúsculas."""
    nfkd = unicodedata.normalize("NFKD", text.lower())
    return "".join(c for c in nfkd if not unicodedata.combining(c))


def is_if(url: str) -> bool:
    """Verifica se a URL pertence a um Instituto Federal."""
    domain = urlparse(url).netloc
    return bool(IF_PATTERN.search(domain))


def get_keywords(url: str) -> list:
    if is_if(url):
        return KEYWORDS_GENERAL + KEYWORDS_IF_BIOLOGY
    return KEYWORDS_GENERAL


# ──────────────────────────────────────────────
# SCRAPING
# ──────────────────────────────────────────────

def fetch(url: str, timeout: int = REQUEST_TIMEOUT):
    """Faz requisição HTTP; retorna (html, url_final) ou (None, msg_erro)."""
    try:
        r = requests.get(url, headers=HEADERS, timeout=timeout,
                         allow_redirects=True, verify=True)
        r.raise_for_status()
        r.encoding = r.apparent_encoding or "utf-8"
        return r.text, r.url
    except requests.exceptions.SSLError:
        try:
            r = requests.get(url, headers=HEADERS, timeout=timeout,
                             allow_redirects=True, verify=False)
            r.encoding = r.apparent_encoding or "utf-8"
            return r.text, r.url
        except Exception as exc:
            return None, f"SSLError: {str(exc)[:120]}"
    except Exception as exc:
        return None, str(exc)[:160]


def find_links(soup: BeautifulSoup, base_url: str) -> list:
    """Retorna links do mesmo domínio que possivelmente levam a páginas de concurso."""
    base_domain = urlparse(base_url).netloc
    seen: set = {base_url}  # exclui a própria página principal
    result: list = []

    for tag in soup.find_all("a", href=True):
        href = str(tag["href"])
        # Strip query string and fragment before checking extension
        last_segment = href.rsplit("/", 1)[-1].split("?")[0].split("#")[0]
        ext = "." + last_segment.rsplit(".", 1)[-1].lower() if "." in last_segment else ""
        if ext in SKIP_EXTENSIONS:
            continue

        text_norm = normalize(tag.get_text(strip=True))
        href_norm = normalize(href)

        for word in LINK_TRIGGERS:
            if word in href_norm or word in text_norm:
                full = urljoin(base_url, href)
                parsed = urlparse(full)
                if (parsed.netloc == base_domain
                        and parsed.scheme in ("http", "https")
                        and full not in seen):
                    seen.add(full)
                    result.append(full)
                break

    return result[:MAX_SUBPAGES]


def search_keywords(text: str, keywords: list) -> list:
    """Retorna subconjunto de keywords presentes no texto (insensível a acentos)."""
    norm = normalize(text)
    return [kw for kw in keywords if normalize(kw) in norm]


def monitor_site(url: str) -> dict:
    """Monitora um único site e retorna dict com os resultados."""
    result: dict = {
        "url": url,
        "status": "error",
        "is_if": is_if(url),
        "matches": [],
        "pages": [],
        "error": None,
    }

    keywords = get_keywords(url)

    # ── Página principal ─────────────────────
    html, final = fetch(url)
    if html is None:
        result["error"] = final
        print(f"  [ERR] {url} → {final}", file=sys.stderr)
        return result

    soup = BeautifulSoup(html, "lxml")
    text = soup.get_text(" ", strip=True)
    found = search_keywords(text, keywords)
    if found:
        result["pages"].append({"url": final, "kws": list(set(found))})
        result["matches"].extend(found)

    # ── Subpáginas relevantes ─────────────────
    visited_subs: set = {final}  # evita reprocessar a página principal ou duplicatas
    for link in find_links(soup, final):
        sub_html, sub_final = fetch(link, timeout=15)
        if sub_html and sub_final not in visited_subs:
            visited_subs.add(sub_final)
            sub_text = BeautifulSoup(sub_html, "lxml").get_text(" ", strip=True)
            sub_found = search_keywords(sub_text, keywords)
            if sub_found:
                result["pages"].append({"url": sub_final, "kws": list(set(sub_found))})
                result["matches"].extend(sub_found)

    result["matches"] = list(set(result["matches"]))
    result["status"] = "found" if result["matches"] else "not_found"

    icon = "✅" if result["matches"] else "⬜"
    print(f"  {icon} {url}  ({len(result['matches'])} ocorrência(s))")
    return result


# ──────────────────────────────────────────────
# GERAÇÃO DO HTML
# ──────────────────────────────────────────────

def _card(r: dict) -> str:
    domain = escape(urlparse(r["url"]).netloc)
    url_attr = escape(r["url"], quote=True)
    cls = "c-found" if r["status"] == "found" else ("c-error" if r["status"] == "error" else "c-none")
    badge = '<span class="badge-if">Instituto Federal</span>' if r["is_if"] else ""
    pill = f'<span class="pill">{len(r["matches"])} ocorrência(s)</span>' if r["matches"] else ""

    pages_html = ""
    if r["pages"]:
        items = "".join(
            f'<li>'
            f'<a href="{escape(p["url"], quote=True)}" target="_blank" rel="noopener noreferrer">{escape(p["url"])}</a>'
            f'<div class="tags">'
            + "".join(f'<span class="tag">{escape(k)}</span>' for k in p["kws"])
            + f'</div></li>'
            for p in r["pages"]
        )
        pages_html = f"<ul>{items}</ul>"

    err_html = f'<p class="errmsg">{escape(str(r["error"]))}</p>' if r.get("error") else ""

    return (
        f'<div class="card {cls}">'
        f'<div class="card-top">'
        f'<div><a href="{url_attr}" target="_blank" rel="noopener noreferrer" class="site-url">{domain}</a>{badge}</div>'
        f"{pill}"
        f"</div>"
        f"{pages_html}{err_html}"
        f"</div>"
    )


def build_html(results: list, ts: str) -> str:
    found = [r for r in results if r["status"] == "found"]
    not_found = [r for r in results if r["status"] == "not_found"]
    errors = [r for r in results if r["status"] == "error"]
    if_found = sum(1 for r in found if r["is_if"])
    total = len(results)

    sections = ""

    if found:
        sections += (
            f'<section>'
            f'<h2><span class="dot dot-green"></span> Com ocorrências '
            f'<span class="section-count">{len(found)}</span></h2>'
            f'<div class="grid">' + "".join(_card(r) for r in found) + "</div>"
            f"</section>"
        )

    if not_found:
        sections += (
            f'<details>'
            f'<summary><h2><span class="dot dot-gray"></span> Sem ocorrências '
            f'<span class="section-count">{len(not_found)}</span></h2></summary>'
            f'<div class="grid">' + "".join(_card(r) for r in not_found) + "</div>"
            f"</details>"
        )

    if errors:
        sections += (
            f'<details>'
            f'<summary><h2><span class="dot dot-red"></span> Erros de acesso '
            f'<span class="section-count">{len(errors)}</span></h2></summary>'
            f'<div class="grid">' + "".join(_card(r) for r in errors) + "</div>"
            f"</details>"
        )

    return f"""<!DOCTYPE html>
<html lang="pt-BR">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Monitor de Concursos Docentes</title>
<script src="https://cdn.counter.dev/script.js" data-id="99568f51-253a-4f49-8638-ab6f1ae2fbe0" data-utcoffset="-3"></script>
<style>{_CSS}</style>
</head>
<body>

<header>
  <h1>&#128218; Monitor de Concursos Docentes</h1>
  <p class="subtitle">Monitoramento automático · Universidades e Institutos Federais · Brasil</p>
  <div class="update-time">Última atualização: {ts}</div>
</header>

<div class="stats">
  <div class="stat">
    <div class="stat-num num-blue">{total}</div>
    <div class="stat-label">Sites monitorados</div>
  </div>
  <div class="stat">
    <div class="stat-num num-green">{len(found)}</div>
    <div class="stat-label">Com ocorrências</div>
  </div>
  <div class="stat">
    <div class="stat-num num-blue">{if_found}</div>
    <div class="stat-label">IFs com Biologia</div>
  </div>
  <div class="stat">
    <div class="stat-num num-red">{len(errors)}</div>
    <div class="stat-label">Erros de acesso</div>
  </div>
</div>

<main>
{sections}
</main>

<footer>
  <p>
    Atualizado automaticamente via
    <a href="https://github.com/features/actions" target="_blank" rel="noopener">GitHub Actions</a>
    &middot; Dados coletados de fontes públicas
  </p>
</footer>

</body>
</html>"""


# ──────────────────────────────────────────────
# MAIN
# ──────────────────────────────────────────────

def main() -> None:
    print("🔍 Monitor de Concursos Docentes")
    print("=" * 50)

    try:
        with open("sites.txt", encoding="utf-8") as f:
            sites = [
                line.strip()
                for line in f
                if line.strip() and not line.strip().startswith("#")
            ]
    except FileNotFoundError:
        print("ERRO: sites.txt não encontrado!", file=sys.stderr)
        sys.exit(1)

    # Garante protocolo em todas as URLs
    sites = [
        url if url.startswith("http") else f"https://{url}"
        for url in sites
    ]

    print(f"📋 {len(sites)} sites para monitorar\n")

    ts = datetime.now(TZ_BRASILIA).strftime("%d/%m/%Y às %H:%M (UTC‑3)")

    results: list = []
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {executor.submit(monitor_site, url): url for url in sites}
        for future in as_completed(futures):
            try:
                results.append(future.result())
            except Exception as exc:
                url = futures[future]
                results.append({
                    "url": url,
                    "status": "error",
                    "is_if": is_if(url),
                    "matches": [],
                    "pages": [],
                    "error": str(exc)[:160],
                })

    # Ordenação: encontrados → sem resultado → erros; dentro de cada grupo,
    # mais ocorrências primeiro
    _order = {"found": 0, "not_found": 1, "error": 2}
    results.sort(key=lambda x: (_order.get(x["status"], 3), -len(x["matches"])))

    html = build_html(results, ts)
    with open("index.html", "w", encoding="utf-8") as f:
        f.write(html)

    n_found = sum(1 for r in results if r["status"] == "found")
    print(f"\n✅ index.html gerado — {n_found}/{len(sites)} sites com ocorrências")


if __name__ == "__main__":
    main()
