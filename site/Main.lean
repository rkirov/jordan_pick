import VersoManual
import Site

open Verso.Genre Manual

/-- Injected verbatim into every page's `<head>` (after `book.css`). -/
def jordanPickTheme : String := r##"
:root {
  --verso-content-max-width: 52rem;
  --verso-font-size: 17px;
  --verso-text-font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Inter", Roboto, Helvetica, Arial, sans-serif;
  --verso-structure-font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Inter", Roboto, Helvetica, Arial, sans-serif;
  --verso-code-font-family: "JetBrains Mono", "SFMono-Regular", "Menlo", "Consolas", monospace;
  --verso-text-color: #1b1f24;
  --verso-structure-color: #0d1117;
  --jp-accent: #0969da;
  --jp-rule: #e6e8eb;
  --jp-code-bg: #f6f8fa;
}
body { line-height: 1.65; }
a { color: var(--jp-accent); text-decoration: none; }
a:hover { text-decoration: underline; }
h1, h2, h3, h4 { letter-spacing: -0.012em; line-height: 1.25; }
.content-wrapper h2 {
  margin-top: 2.2rem; padding-bottom: 0.3rem;
  border-bottom: 1px solid var(--jp-rule);
}
.content-wrapper h3 { margin-top: 1.6rem; }
pre {
  background: var(--jp-code-bg);
  border: 1px solid var(--jp-rule);
  border-radius: 8px;
  padding: 0.85rem 1rem;
  overflow-x: auto;
  font-size: 0.86em;
  line-height: 1.5;
}
:not(pre) > code {
  background: var(--jp-code-bg);
  border: 1px solid var(--jp-rule);
  border-radius: 5px;
  padding: 0.08em 0.34em;
  font-size: 0.9em;
}
.titlepage h1 {
  font-size: 2.5rem; font-weight: 800;
  border-bottom: 3px solid var(--jp-accent);
  padding-bottom: 0.6rem; margin-bottom: 0.4rem;
}
.titlepage .authors { color: #57606a; }
nav#toc .split-toc .title > a:hover { color: var(--jp-accent); }
header { border-bottom: 1px solid var(--jp-rule); }
"##

def main := manualMain (%doc Site) (config := {
  emitHtmlSingle := .no,
  emitHtmlMulti := .immediately,
  htmlDepth := 2,
  sourceLink := some "https://github.com/rkirov/jordan-pick",
  issueLink := some "https://github.com/rkirov/jordan-pick/issues",
  extraHead := #[Verso.Output.Html.tag "style" #[] (Verso.Output.Html.text false jordanPickTheme)]
})
