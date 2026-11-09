/*
 * Shared front-end for all problem pages.
 *
 * A problem page sets <body data-problem="..."> and contains an empty
 * <section id="results">; this script builds the filters, the Delta panel and the
 * results table inside it. The landing page only uses the result counts.
 */
(function () {
  "use strict";

  const data = window.ATLAS_DATA || { papers: {}, results: [] };
  const A = window.Asymptotics;
  const PROBLEM = document.body.dataset.problem;

  // ---------- vocabulary ----------

  const GRAPH_CLASSES = {
    general: "General graphs",
    "bounded-degree": "Constant-degree graphs",
    "growth-bounded": "Growth-bounded graphs",
    "bounded-arboricity": "Bounded-arboricity graphs",
    "girth-7": "Graphs of girth ≥ 7",
    bipartite: "Bipartite graphs",
    trees: "Trees",
    paths: "Paths",
    cycles: "Cycles",
  };
  // Each class's direct superclasses: a result for a superclass also holds for the class.
  const CLASS_PARENTS = {
    "bounded-degree": ["bounded-arboricity"], "growth-bounded": ["general"],
    "bounded-arboricity": ["general"], "girth-7": ["general"],
    bipartite: ["general"], trees: ["bipartite", "bounded-arboricity", "girth-7"],
    paths: ["trees"], cycles: ["bounded-arboricity"],
  };
  // Classes that fix the value of Delta (cycles and paths have Delta <= 2): results for them only make sense in these regimes.
  const CLASS_REGIMES = { "bounded-degree": ["const"], cycles: ["const"], paths: ["const"] };
  const ASSUMPTIONS = {
    "given-2-coloring": "Given a 2-coloring",
    "given-orientation-towards-root": "Given orientation towards root",
    "max-degree-log21": "Δ = ω(log²¹ n)",
    "min-degree-log7": "Min. degree Ω(log⁷ n)",
    "max-degree-log": "Δ = Ω(log n)",
    "max-degree-log1delta": "Δ = Ω(log^(1+δ) n)",
    "max-degree-constant": "Δ ≥ Δ₀ (large constant)",
    "max-degree-poly": "Δ = n^Ω(1)",
    "eps-greater-inverse-delta": "ε > 1/Δ",
  };
  // Assumptions that bound Delta from below: results relying on them only apply in these regimes.
  const LARGE_DELTA = ["exp14", "exp13", "exp12", "exp23", "nk", "n"];
  const ASSUMPTION_REGIMES = {
    "max-degree-log21": LARGE_DELTA, "min-degree-log7": LARGE_DELTA,
    "max-degree-log": ["log", "log2", "log3", ...LARGE_DELTA],
    "max-degree-log1delta": ["log2", "log3", ...LARGE_DELTA],
    "max-degree-poly": ["nk", "n"],
  };

  // Lower bounds on the degree imply weaker ones: a result assuming the weaker bound also applies.
  const ALL_CLASSES = "__all";   // marks the "All" option of the graph class filter

  const ASSUMPTION_IMPLIES = {
    "max-degree-poly": ["max-degree-log21", "max-degree-log1delta", "max-degree-log", "max-degree-constant"],
    "max-degree-log21": ["max-degree-log1delta", "max-degree-log", "max-degree-constant"],
    "min-degree-log7": ["max-degree-log1delta", "max-degree-log", "max-degree-constant"],
    "max-degree-log1delta": ["max-degree-log", "max-degree-constant"],
    "max-degree-log": ["max-degree-constant"],
  };
  const assumptionClosure = (list) => new Set((list || []).flatMap((a) => [a, ...(ASSUMPTION_IMPLIES[a] || [])]));

  // A lower bound for a class with small Delta (e.g. Omega(log* n) on cycles) also holds for every larger Delta,
  // since graphs of maximum degree at most Delta include that class, as long as neither the bound nor the problem
  // depends on Delta. Colorings are excluded: their palette grows with Delta, which can make them easier.
  const holdsForAllDelta = (r) => r.bound === "lower" && !r.colors && !/\bDelta\b/.test(r.runtime.expr);

  // Regimes of Delta a result applies in, or null for all of them.
  function allowedRegimes(r) {
    const limits = [holdsForAllDelta(r) ? null : CLASS_REGIMES[r.graph_class],
      ...(r.assumptions || []).map((a) => ASSUMPTION_REGIMES[a])]
      .filter(Boolean);
    if (!limits.length) return null;
    return limits.reduce((acc, ids) => acc.filter((id) => ids.includes(id)));
  }

  // Colorings with different numbers of colors are different problems; the key identifies the count.
  const colorsKey = (r) => (r.colors ? r.colors.expr.replace(/\s+/g, "") : null);
  // Options of the Colors filter, per problem, as a hierarchy: an option shows the results of all options
  // below it (palettes of at most that size). `keys` are the exact color counts (colorsKey) placed at a
  // node; other counts fall back to their growth class (see colorGroup), or to "all" if the tree lacks it.
  const COLOR_TREES = {
    "vertex-coloring": {
      initial: { id: "delta1", exact: true },     // the Colors filter starts at exactly Delta + 1
      nodes: [
        { id: "all", parent: null, label: "All" },
        { id: "exp", parent: "all", latex: "\\exp(\\Delta)" },
        { id: "poly", parent: "exp", latex: "\\mathrm{poly}(\\Delta)" },
        { id: "linear", parent: "poly", latex: "\\text{linear in } \\Delta" },
        { id: "delta1", parent: "linear", latex: "\\Delta + 1", keys: ["Delta+1"] },
        // A chain below O(Delta): each palette option also lists the smaller palettes below it.
        { id: "delta", parent: "delta1", latex: "\\Delta", keys: ["Delta"] },
        { id: "const", parent: "delta", latex: "\\mathcal{O}(1)" },
      ],
    },
    "edge-coloring": {
      initial: { id: "two1", exact: true },       // the Colors filter starts at exactly 2Delta - 1
      fallback: { poly: "more", exp: "more" },   // growth classes of palettes not listed under `keys`
      nodes: [
        // (1+eps)Delta + O(sqrt(log n)) grows with n and fits no option below, so it is only under "All".
        { id: "all", parent: null, label: "All", keys: ["(1+eps)*Delta+O(sqrt(log(n)))"] },
        // Everything with more than 2Delta - 1 colors, as one option without an "exactly" mode.
        { id: "more", parent: "all", order: 0, latex: "> 2\\Delta - 1", single: true,
          keys: ["(2+eps)*Delta", "(8+eps)*Delta", "O(Delta^(1+eps))", "O(Delta*log(n))", "1.6*Delta+O(log(n)^(1+delta))"] },
        { id: "two1", parent: "all", order: 1, latex: "2\\Delta - 1", keys: ["2*Delta-1"] },
        { id: "two2", parent: "two1", latex: "2\\Delta - 2", keys: ["2*Delta-2"] },
        { id: "threehalveseps", parent: "two2", latex: "(3/2+\\varepsilon)\\Delta", keys: ["(3/2+eps)*Delta"] },
        { id: "threehalves", parent: "threehalveseps", latex: "3\\Delta/2", keys: ["3*Delta/2"] },
        { id: "eps", parent: "threehalves", latex: "(1+\\varepsilon)\\Delta", keys: ["(1+eps)*Delta"] },
        { id: "sqrt", parent: "eps", latex: "\\Delta + \\mathcal{O}(\\sqrt{\\Delta})",
          keys: ["Delta+O(sqrt(Delta))", "Delta+Otilde(sqrt(Delta))"] },
        { id: "o1", parent: "sqrt", latex: "\\Delta + \\mathcal{O}(1)", keys: ["Delta+2", "Delta+O(1)"] },
        { id: "delta1", parent: "o1", latex: "\\Delta + 1", keys: ["Delta+1"] },
        { id: "delta", parent: "delta1", latex: "\\Delta", keys: ["Delta"] },   // e.g. trees, bipartite graphs
        // Delta + O(log n) also contains the Delta + O(1) palettes (`includes`), besides its own.
        { id: "logn", parent: "all", order: 2, latex: "\\Delta + \\mathcal{O}(\\log n)", includes: ["o1"],
          keys: ["Delta+O(log(n))", "Delta+O(log(n)/log(log(n)))"] },
      ],
    },
  };
  const COLOR_TREE = (COLOR_TREES[PROBLEM] || COLOR_TREES["vertex-coloring"]).nodes;
  const COLOR_FALLBACK = (COLOR_TREES[PROBLEM] || COLOR_TREES["vertex-coloring"]).fallback || {};
  const COLOR_NODE = Object.fromEntries(COLOR_TREE.map((n) => [n.id, n]));
  const RANDOMNESS_RANK = { deterministic: 0, randomized: 1 };
  const MODEL_RANK = { CONGEST: 0, LOCAL: 1 };   // a CONGEST algorithm also runs in LOCAL

  // ---------- DOM helpers ----------

  function el(tag, attrs, children) {
    const node = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs || {})) {
      if (v === undefined || v === null) continue;
      if (k === "class") node.className = v;
      else if (k === "text") node.textContent = v;
      else node.setAttribute(k, v);
    }
    for (const c of children || []) node.append(c);
    return node;
  }

  function tex(latex, cls) {
    const span = el("span", { class: cls });
    if (window.katex) window.katex.render(latex, span, { throwOnError: false });
    else span.textContent = latex;
    return span;
  }

  // Roughly how many characters a formula takes when rendered (commands like \log count as their text).
  function visibleLength(latex) {
    return latex
      .replace(/\\(left|right|mathcal|mathrm|widetilde|text|operatorname|displaystyle)\b/g, "")
      .replace(/\\(log|max|min|poly|exp)\b/g, (m) => m.slice(1))
      .replace(/\\[a-zA-Z]+/g, "x")
      .replace(/\\[,;!: ]/g, "")
      .replace(/[{}\s^_]/g, "").length;
  }

  // A runtime formula, set smaller when it is long, so the runtime column stays narrow.
  function runtimeTex(latex) {
    const n = visibleLength(latex);
    return tex(latex, n > 44 ? "runtime runtime-xlong" : n > 30 ? "runtime runtime-long" : "runtime");
  }

  function humanize(slug) {
    const s = slug.replace(/-/g, " ");
    return s.charAt(0).toUpperCase() + s.slice(1);
  }

  function renderMath(root) {
    if (root && window.renderMathInElement) {
      window.renderMathInElement(root, { delimiters: [{ left: "$", right: "$", display: false }], throwOnError: false });
    }
  }

  // ---------- shared page parts ----------

  const PROBLEMS = {
    "maximal-matching": { name: "Maximal matching", page: "maximal-matching.html" },
    mis: { name: "MIS", page: "mis.html" },
    "vertex-coloring": { name: "Vertex coloring", page: "vertex-coloring.html" },
    "edge-coloring": { name: "Edge coloring", page: "edge-coloring.html" },
    "network-decomposition": { name: "Network decomposition", page: "network-decomposition.html" },
  };
  const problemInfo = (id) => PROBLEMS[id] || { name: humanize(id), page: null };

  function problemLink(id, text) {
    const p = problemInfo(id);
    return p.page ? el("a", { href: p.page, text: text || p.name }) : el("span", { text: text || p.name });
  }

  function modelChips(models) {
    return models.map((m) => el("span", { class: "chip model", text: m }));
  }

  // Table cell listing the papers of a result or reduction; no sources means folklore.
  // A comment as nodes; "[[result-id]]" becomes a link to that result on its problem page, labelled with
  // its paper, like the result a reduction is applied to ("[[paper-id]]" links a paper as in the Source column).
  function commentNodes(text) {
    return text.split(/(\[\[[a-z0-9-]+\]\])/).filter(Boolean).map((part) => {
      const ref = part.match(/^\[\[([a-z0-9-]+)\]\]$/);
      if (!ref) return document.createTextNode(part);
      const result = data.results.find((x) => x.id === ref[1]);
      if (result) {
        const paper = result.sources && data.papers[result.sources[0].paper];
        const label = paper ? paper.label : result.title;
        const page = problemInfo(result.problem).page;
        return page ? el("a", { href: `${page}#${result.id}`, title: result.title, text: label })
          : el("span", { title: result.title, text: label });
      }
      const paper = data.papers[ref[1]];
      if (!paper) return document.createTextNode(part);
      const tooltip = `${paper.title}\n${paper.authors.join(", ")}`;
      return paper.public_url
        ? el("a", { href: paper.public_url, title: tooltip, target: "_blank", rel: "noopener", text: paper.label })
        : el("span", { title: tooltip, text: paper.label });
    });
  }

  function sourceCell(sources) {
    const cell = el("td", { class: "col-source" });
    if (!sources || !sources.length) {
      cell.append(el("span", { class: "folklore", text: "Folklore" }));
      return cell;
    }
    sources.forEach((s, i) => {
      const paper = data.papers[s.paper];
      const block = el("div");
      if (!paper) {
        block.append(el("span", { class: "label", text: s.paper }));
      } else {
        const tooltip = `${paper.title}\n${paper.authors.join(", ")}`;
        block.append(paper.public_url
          ? el("a", { href: paper.public_url, title: tooltip, target: "_blank", rel: "noopener", text: paper.label })
          : el("span", { class: "label", title: tooltip, text: paper.label }));
        const venues = paper.versions.filter((v) => v.type !== "preprint").map((v) => `${v.venue} ${v.year}`).join(" · ");
        // The reference ("Theorem 1.3") links to the theorem itself when the source has a url.
        const reference = !s.reference ? null
          : s.url ? el("a", { class: "theorem-link", href: s.url, target: "_blank", rel: "noopener",
                              title: "Open this theorem in the paper", text: s.reference })
            : document.createTextNode(s.reference);
        const parts = [venues ? document.createTextNode(venues) : null, reference].filter(Boolean);
        // A paper with only preprint versions (arXiv or a manuscript) has not been peer-reviewed yet.
        const preprint = paper.versions.every((v) => v.type === "preprint")
          ? el("span", { class: "chip preprint", title: "Not yet peer-reviewed", text: "Preprint" }) : null;
        if (parts.length || preprint) {
          const sub = el("span", { class: "sub" });
          if (preprint) sub.append(preprint);
          parts.forEach((p, i) => { if (i) sub.append(" · "); sub.append(p); });
          block.append(sub);
        }
      }
      if (i > 0) block.style.marginTop = "6px";
      cell.append(block);
    });
    return cell;
  }

  const FOOTER_DECOMPOSITION = `
    Only algorithms for general graphs are marked. One is state of the art if no other result matching the filters is at least as good in
    runtime, number of colors and cluster diameter at the same time, and better in one of them. A strong-diameter
    decomposition counts as at least as good as a weak-diameter one with the same parameters, a deterministic result
    also counts for randomized algorithms, and a CONGEST result also counts for LOCAL.
    Parameters such as λ are treated as fixed constants when comparing.
    Results obtained by a reduction from another problem say so in the Comments column (see Reductions).`;

  const FOOTER = `
    “State of the art for” compares the results at sample values of Δ (from constant through log* n, polylogarithmic and
    quasi-polylogarithmic to polynomial), so the ranges shown are approximate.
    A result that ties for the best somewhere is still not state of the art if another result is at least as fast
    for every Δ and faster for some Δ (e.g. O(Δ²) + log* n next to O(√Δ) + log* n).
    Only the results that match the current filters are compared, so the state of the art is the best among them.
    Only algorithms for general graphs are marked; algorithms for smaller graph classes are listed but not ranked.
    The randomness filter lists only algorithms of that kind. A CONGEST result also counts for LOCAL, and a result
    without an assumption also counts where the assumption holds.
    For colorings, only results with the same number of colors are compared.
    Results obtained by a reduction from another problem say so in the Comments column (see Reductions).`;

  const FOOTER_LOWER = `
    “State of the art for” compares the lower bounds at sample values of Δ (from constant through log* n, polylogarithmic and
    quasi-polylogarithmic to polynomial), so the ranges shown are approximate.
    A lower bound is marked as state of the art if no other lower bound matching the filters is stronger, neither
    for some Δ alone nor for every Δ at once (at least as strong everywhere and stronger somewhere).
    A lower bound counts in every setting it applies to, which is the reverse of algorithms: a lower bound for randomized
    algorithms also holds for deterministic ones, a LOCAL lower bound also holds in CONGEST, and a lower bound for a
    graph class also holds for its superclasses (e.g. trees for general graphs). The randomness and model filters list
    every lower bound that holds in the chosen setting; the graph class filter lists the bounds stated for that class.
    With all classes shown, the lower bounds are compared as bounds for general graphs, so a bound for cycles competes
    with one for trees. A bound for cycles, paths or bounded-degree graphs that does not involve Δ (such as
    Ω(log* n)) holds for every Δ, except for colorings, whose palette grows with Δ.`;

  const RESULTS_TEMPLATE = `
    <div class="results-head">
      <h2 id="results-title" class="visually-hidden">Results</h2>
      <div class="bound-tabs" role="tablist" aria-labelledby="results-title">
        <button type="button" role="tab" data-bound="upper" aria-selected="true">Algorithms <span class="pill-count"></span></button>
        <button type="button" role="tab" data-bound="lower" aria-selected="false">Lower bounds <span class="pill-count"></span></button>
      </div>
      <p class="count" id="result-count" aria-live="polite"></p>
    </div>

    <div class="filter-bar" id="filter-bar">
      <div class="filter-item" id="randomness-group" data-options>
        <button type="button" class="filter-toggle" aria-expanded="false" aria-controls="fp-randomness">
          <span class="filter-label">Randomness</span>
          <span class="filter-value" id="fv-randomness"></span>
          <span class="chevron" aria-hidden="true"></span>
        </button>
        <div class="filter-popover" id="fp-randomness" role="group" aria-label="Randomness" hidden>
          <div class="segmented" data-key="randomness">
            <button type="button" data-value="deterministic" aria-pressed="true">Deterministic</button>
            <button type="button" data-value="randomized" aria-pressed="false">Randomized</button>
          </div>
        </div>
      </div>
      <div class="filter-item" id="model-group" data-options>
        <button type="button" class="filter-toggle" aria-expanded="false" aria-controls="fp-model">
          <span class="filter-label">Model</span>
          <span class="filter-value" id="fv-model"></span>
          <span class="chevron" aria-hidden="true"></span>
        </button>
        <div class="filter-popover" id="fp-model" role="group" aria-label="Model" hidden>
          <div class="segmented" data-key="model">
            <button type="button" data-value="LOCAL" aria-pressed="true">LOCAL</button>
            <button type="button" data-value="CONGEST" aria-pressed="false">CONGEST</button>
          </div>
        </div>
      </div>
      <div class="filter-item" id="diameter-group" data-options hidden>
        <button type="button" class="filter-toggle" aria-expanded="false" aria-controls="fp-diameter">
          <span class="filter-label">Diameter</span>
          <span class="filter-value" id="fv-diameter"></span>
          <span class="chevron" aria-hidden="true"></span>
        </button>
        <div class="filter-popover" id="fp-diameter" role="group" aria-label="Diameter" hidden>
          <div class="segmented" data-key="diameter">
            <button type="button" data-value="all" aria-pressed="true">All</button>
            <button type="button" data-value="strong" aria-pressed="false">Strong</button>
          </div>
        </div>
      </div>
      <div class="filter-item is-wide" id="colors-group" data-options hidden>
        <button type="button" class="filter-toggle" aria-expanded="false" aria-controls="fp-colors">
          <span class="filter-label">Colors</span>
          <span class="filter-value" id="fv-colors"></span>
          <span class="chevron" aria-hidden="true"></span>
        </button>
        <div class="filter-popover" id="fp-colors" role="group" aria-label="Colors" hidden>
          <div class="pills" id="colors-filter"></div>
        </div>
      </div>
      <div class="filter-item is-wide" id="classes-group" data-options>
        <button type="button" class="filter-toggle" aria-expanded="false" aria-controls="fp-classes">
          <span class="filter-label">Graph classes</span>
          <span class="filter-value" id="fv-classes"></span>
          <span class="chevron" aria-hidden="true"></span>
        </button>
        <div class="filter-popover" id="fp-classes" role="group" aria-label="Graph classes" hidden>
          <div class="pills" id="class-filter"></div>
        </div>
      </div>
      <div class="filter-item is-wide" id="years-group" hidden>
        <button type="button" class="filter-toggle" aria-expanded="false" aria-controls="fp-years">
          <span class="filter-label">Years</span>
          <span class="filter-value" id="timeline-value" aria-live="polite"></span>
          <span class="chevron" aria-hidden="true"></span>
        </button>
        <div class="filter-popover" id="fp-years" role="group" aria-label="Years" hidden>
          <div id="timelines"></div>
        </div>
      </div>
      <div class="filter-item is-wide" id="regime-panel">
        <button type="button" class="filter-toggle" aria-expanded="false" aria-controls="fp-regime">
          <span class="filter-label">Max. degree Δ</span>
          <span class="filter-value" id="regime-value"></span>
          <span class="chevron" aria-hidden="true"></span>
        </button>
        <div class="filter-popover" id="fp-regime" role="group" aria-label="Max. degree Δ" hidden>
          <input type="range" id="regime-slider" min="0" max="5" step="1" value="0"
                 aria-describedby="regime-note" aria-label="Asymptotic value of the maximum degree">
          <div class="regime-ticks" id="regime-ticks"></div>
        </div>
      </div>
      <label class="only-best">
        <input type="checkbox" id="only-best"> Only state of the art
      </label>
    </div>
    <p class="regime-note" id="regime-note"></p>

    <div class="table-scroll">
      <table class="results-table">
        <thead>
          <tr>
            <th scope="col" class="col-year"><button type="button" class="sort" id="sort-year" aria-label="Sort by year">Year <span aria-hidden="true" id="sort-arrow">↓</span></button></th>
            <th scope="col"><button type="button" class="sort" id="sort-runtime">Runtime</button></th>
            <th scope="col" id="best-col">State of the art for</th>
            <th scope="col">Model</th>
            <th scope="col">Graph class</th>
            <th scope="col">Source</th>
            <th scope="col">Comments</th>
            <th scope="col" class="col-edit"><span class="visually-hidden">Edit or report</span></th>
          </tr>
        </thead>
        <tbody id="results-body"></tbody>
      </table>
    </div>
    <p class="empty" id="results-empty" hidden>No results match these filters.</p>
    <div class="missing-report entry-report">
      <button type="button" class="missing-btn" id="missing-btn" aria-expanded="false">
        <span class="missing-plus" aria-hidden="true"></span><span id="missing-label">Report missing algorithm</span>
      </button>
      <div class="missing-slot" id="missing-slot"></div>
    </div>`;

  // ---------- edit forms (papers in the bibliography, results in the tables) ----------
  // Every entry gets two buttons, and only one of them is shown. With scripts/serve.py running, /api/status
  // answers and <html data-editable> shows "Edit", whose form saves to data/. On the public site (GitHub Pages,
  // no server) the request fails and "Report an issue" is shown instead; it opens a prefilled GitHub issue.

  const REPO = "florian-schager/atlas";
  let editable = false;
  fetch("api/status").then((r) => (r.ok ? r.json() : null)).then((s) => {
    editable = !!(s && s.editable);
    document.documentElement.toggleAttribute("data-editable", editable);
  }).catch(() => {});

  function yamlScalar(v) {
    if (typeof v === "number" || typeof v === "boolean") return String(v);
    const s = String(v);
    const plain = /^[A-Za-z(Δ\\][^:#{}[\],&*!|>'"%@`]*$/.test(s) && !/\s$/.test(s)
      && !/^(true|false|null|yes|no|on|off)$/i.test(s);
    return plain ? s : JSON.stringify(s);
  }

  // YAML for an entry: nested objects and lists of objects, in the order of the keys given.
  function toYaml(value, indent = "") {
    const lines = [];
    for (const [k, v] of Object.entries(value)) {
      if (Array.isArray(v)) {
        lines.push(`${indent}${k}:`);
        for (const item of v) {
          if (item && typeof item === "object") {
            const inner = toYaml(item, `${indent}  `).split("\n").filter(Boolean);
            lines.push(`${indent}- ${inner[0].trimStart()}`, ...inner.slice(1));
          } else {
            lines.push(`${indent}- ${yamlScalar(item)}`);
          }
        }
      } else if (v && typeof v === "object") {
        lines.push(`${indent}${k}:`, toYaml(v, `${indent}  `).replace(/\n$/, ""));
      } else {
        lines.push(`${indent}${k}: ${yamlScalar(v)}`);
      }
    }
    return lines.join("\n") + "\n";
  }

  const options = (pairs, selected) => pairs.map(([value, text]) =>
    el("option", { value, selected: value === selected ? "" : null, text }));

  function field(label, input) {
    return el("label", { class: "bib-field" }, [el("span", { text: label }), input]);
  }

  function removeButton(row) {
    const b = el("button", { type: "button", class: "bib-remove", title: "Remove", "aria-label": "Remove", text: "×" });
    b.addEventListener("click", () => row.remove());
    return b;
  }

  // Save an entry through serve.py (then reload at `hash`), or show its YAML when saving is not available.
  async function saveEntry(kind, id, entry, status, yamlBox, hash) {
    if (!editable) {
      yamlBox.textContent = toYaml(entry);
      yamlBox.hidden = false;
      status.textContent = `Saving needs scripts/serve.py. Copy this into data/${kind}/${id}.yaml:`;
      return;
    }
    status.textContent = "Saving…";
    try {
      const res = await fetch(`api/${kind}/${id}`, {
        method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(entry),
      });
      const reply = await res.json();
      if (!res.ok) { status.textContent = `Not saved: ${(reply.errors || ["unknown error"]).join("; ")}`; return; }
      status.textContent = `Saved to ${reply.saved}. Reloading…`;
      if (hash) location.hash = hash;
      location.reload();
    } catch (err) {
      status.textContent = `Not saved: ${err.message}`;
    }
  }

  // For a result obtained by a reduction, in the Comments column: a chip for the reduction ("via MIS", or the
  // technique for a reduction within one problem, e.g. "Shattering"), an arrow, and a chip for the result it is
  // applied to ("GG, 2024"). The first links to the reduction on the Reductions page, the second to the result.
  function reductionChips(r) {
    if (!r.reduce_to) return null;
    const target = data.results.find((x) => x.id === r.reduce_to);
    if (!target) return el("span", { class: "reduction-chips" }, [el("span", { class: "chip via", text: `via ${r.reduce_to}` })]);
    const p = problemInfo(target.problem);
    const used = reductionFor(r, target);
    const sameProblem = target.problem === r.problem;
    // An algorithm comes from a reduction *to* the target's problem, a lower bound from a reduction *from* it.
    const name = target.colors && /^\d+$/.test(target.colors.latex) ? `${target.colors.latex}-coloring` : p.name;
    const text = sameProblem ? (used ? used.title : "Reduction") : `via ${name}`;
    const title = sameProblem ? `Obtained from another ${p.name} result${used ? ` by ${used.title.toLowerCase()}` : ""}`
      : `Obtained by a reduction ${r.bound === "lower" ? "from" : "to"} ${name}${used ? ` (${used.title.toLowerCase()})` : ""}`;
    const via = used
      ? el("a", { class: "chip via", href: `reductions.html#${used.id}`, title, text })
      : el("span", { class: "chip via", title, text });

    const paper = target.sources && data.papers[target.sources[0].paper];
    const label = paper ? paper.label : target.title;
    const resultTitle = `Applied to: ${target.title}${paper ? ` (${paper.label})` : ""}`;
    const result = p.page
      ? el("a", { class: "chip result", href: `${p.page}#${target.id}`, title: resultTitle, text: label })
      : el("span", { class: "chip result", title: resultTitle, text: label });
    return el("span", { class: "reduction-chips" }, [
      via,
      // The arrow stays with the result chip, so a wrapped pair reads "via MIS" / "→ GG, 2024".
      el("span", { class: "reduction-target" }, [
        el("span", { class: "reduction-arrow", "aria-hidden": "true", text: "→" }),
        el("span", { class: "visually-hidden", text: "applied to" }),
        result,
      ]),
    ]);
  }

  // The reduction that turns result `target` into result r (see data/reductions/): for an algorithm one from
  // r's problem to the target's, for a lower bound one from the target's problem to r's.
  function reductionFor(r, target) {
    if (r.via) return (data.reductions || []).find((x) => x.id === r.via);
    const [src, dst] = r.bound === "lower" ? [target.problem, r.problem] : [r.problem, target.problem];
    return (data.reductions || []).find((x) => x.from.problem === src && x.to.problem === dst
      && x.models.includes(r.model) && (!x.graph_class || x.graph_class === r.graph_class));
  }

  // Results that a result of `problem` can be derived from (see data/reductions/): algorithms for problems
  // it reduces to, or lower bounds for problems that reduce to it.
  function reductionTargets(problem, bound) {
    const lower = bound === "lower";
    const to = new Set((data.reductions || []).filter((x) => (lower ? x.to : x.from).problem === problem)
      .map((x) => (lower ? x.from : x.to).problem));
    return data.results.filter((x) => to.has(x.problem) && x.bound === bound)
      .map((x) => [x.id, `${problemInfo(x.problem).name}: ${x.title} (${(data.papers[x.sources[0].paper] || {}).label || x.sources[0].paper})`])
      .sort((a, b) => a[1].localeCompare(b[1]));
  }

  // Open (or close) the edit form for result r in a table row below its row `tr`.
  function toggleResultForm(r, tr, btn) {
    const next = tr.nextElementSibling;
    if (next && next.classList.contains("edit-row")) {
      next.remove();
      btn.setAttribute("aria-expanded", "false");
      return;
    }
    btn.setAttribute("aria-expanded", "true");
    const close = () => { editRow.remove(); btn.setAttribute("aria-expanded", "false"); };

    const input = (value, attrs) => el("input", { value: value ?? "", ...attrs });
    const select = (pairs, selected, attrs) => el("select", attrs || {}, options(pairs, selected));
    const exprPair = (label, x) => {
      const latex = input(x && x.latex, { "aria-label": `${label} (LaTeX)`, placeholder: "LaTeX" });
      const expr = input(x && x.expr, { "aria-label": `${label} (expression)`, placeholder: "Expression, e.g. O(log(n))" });
      return { latex, expr, node: field(label, el("div", { class: "bib-row expr-pair" }, [latex, expr])) };
    };

    const title = input(r.title, { "aria-label": "Title" });
    const reduceTo = select([["", "— (solves the problem directly)"], ...reductionTargets(r.problem, r.bound)], r.reduce_to || "",
                            { "aria-label": "Reduction to" });
    const runtime = exprPair("Runtime", r.runtime);
    const preview = el("div", { class: "runtime-preview" });
    const showPreview = () => preview.replaceChildren(tex(runtime.latex.value || " "));
    runtime.latex.addEventListener("input", showPreview);
    showPreview();

    const isColoring = r.problem === "vertex-coloring" || r.problem === "edge-coloring";
    const colors = isColoring ? exprPair("Colors", r.colors) : null;
    const dec = r.decomposition || null;
    const decColors = r.problem === "network-decomposition" ? exprPair("Colors", dec && dec.colors) : null;
    const decDiameter = r.problem === "network-decomposition" ? exprPair("Diameter", dec && dec.diameter) : null;
    const decType = r.problem === "network-decomposition"
      ? select([["weak", "Weak"], ["strong", "Strong"]], dec && dec.diameter_type, { "aria-label": "Diameter type" }) : null;

    const bound = select([["upper", "Upper bound"], ["lower", "Lower bound"]], r.bound);
    const model = select([["LOCAL", "LOCAL"], ["CONGEST", "CONGEST"]], r.model);
    const randomness = select([["deterministic", "Deterministic"], ["randomized", "Randomized"]], r.randomness);
    const graphClass = select(Object.entries(GRAPH_CLASSES), r.graph_class);
    const year = input(r.year, { type: "number", min: "1900", max: "2100", class: "bib-year" });
    const status = select([["approved", "Approved"], ["pending", "Pending"], ["rejected", "Rejected"]], r.status);

    const assumptions = el("div", { class: "checks assumption-checks" }, Object.entries(ASSUMPTIONS).map(([id, text]) =>
      el("label", {}, [el("input", { type: "checkbox", value: id, checked: (r.assumptions || []).includes(id) ? "" : null }), text])));

    const paperChoices = Object.values(data.papers).map((p) => [p.id, `${p.label} — ${p.title}`])
      .sort((a, b) => a[1].localeCompare(b[1]));
    const sourceRow = (s) => {
      const row = el("div", { class: "bib-row source-row" });
      row.append(select(paperChoices, s.paper, { "data-k": "paper", "aria-label": "Paper" }),
        input(s.reference, { "data-k": "reference", placeholder: "Reference, e.g. Theorem 1.3", "aria-label": "Reference" }),
        input(s.url, { "data-k": "url", placeholder: "Link to the theorem", "aria-label": "Link", type: "url" }),
        removeButton(row));
      return row;
    };
    const sources = el("div", { class: "bib-rows" }, (r.sources || []).map(sourceRow));
    const addSource = el("button", { type: "button", class: "bib-add", text: "+ Source" });
    addSource.addEventListener("click", () => sources.append(sourceRow({ paper: paperChoices[0][0] })));
    const comments = input(r.comments, { maxlength: "80", "aria-label": "Comments" });

    const statusLine = el("p", { class: "bib-status", "aria-live": "polite" });
    const yamlBox = el("pre", { class: "bib-yaml", hidden: "" });
    const save = el("button", { type: "submit", class: "bib-save", text: editable ? "Save" : "Show YAML" });
    const cancel = el("button", { type: "button", class: "bib-cancel", text: "Cancel" });
    cancel.addEventListener("click", close);

    const parameterFields = [
      colors && colors.node, decColors && decColors.node, decDiameter && decDiameter.node,
      decType && field("Diameter type", decType),
    ].filter(Boolean);
    const form = el("form", { class: "bib-form result-form" }, [
      field("Title", title),
      field("Reduction to", reduceTo),
      runtime.node, preview,
      ...parameterFields,
      el("div", { class: "bib-row result-selects" }, [
        field("Bound", bound), field("Model", model), field("Randomness", randomness),
        field("Graph class", graphClass), field("Year", year), field("Status", status),
      ]),
      el("fieldset", {}, [el("legend", { text: "Assumptions" }), assumptions]),
      el("fieldset", {}, [el("legend", { text: "Sources" }), sources, addSource]),
      field("Comments (short, no full sentence)", comments),
      el("div", { class: "bib-actions" }, [save, cancel, statusLine]),
      yamlBox,
    ]);

    form.addEventListener("submit", async (e) => {
      e.preventDefault();
      const pair = (p) => ({ latex: p.latex.value.trim(), expr: p.expr.value.trim() });
      // Check the expressions with the site's own parser before saving, so the pages keep working.
      const exprs = [["Runtime", runtime], ["Colors", colors], ["Colors", decColors], ["Diameter", decDiameter]]
        .filter(([, p]) => p);
      for (const [label, p] of exprs) {
        try { A.parse(p.expr.value.trim()); } catch (err) {
          statusLine.textContent = `Not saved: ${label} expression: ${err.message}`;
          return;
        }
      }
      const out = { id: r.id, title: title.value.trim(), problem: r.problem };
      if (reduceTo.value) out.reduce_to = reduceTo.value;
      if (decColors) {
        out.decomposition = { colors: pair(decColors), diameter: pair(decDiameter), diameter_type: decType.value };
      }
      if (colors) out.colors = pair(colors);
      Object.assign(out, { bound: bound.value, model: model.value, randomness: randomness.value,
                           graph_class: graphClass.value });
      const chosen = [...assumptions.querySelectorAll("input:checked")].map((c) => c.value);
      if (chosen.length) out.assumptions = chosen;
      out.runtime = pair(runtime);
      out.year = Number(year.value);
      out.sources = [...sources.querySelectorAll(".source-row")].map((row) => {
        const s = {};
        for (const inp of row.querySelectorAll("[data-k]")) if (inp.value.trim()) s[inp.dataset.k] = inp.value.trim();
        return s;
      });
      if (comments.value.trim()) out.comments = comments.value.trim();
      out.status = status.value;
      await saveEntry("results", r.id, out, statusLine, yamlBox, r.id);
    });

    const editRow = el("tr", { class: "edit-row" }, [el("td", { colspan: String(tr.children.length) }, [form])]);
    tr.after(editRow);
    title.focus();
  }

  // ---------- reporting an issue (public site) ----------

  const REPORT_TOPICS = [
    { short: "Runtime", label: "Issue with runtime",
      hint: "e.g. the runtime, model, randomness or graph class is stated wrongly" },
    { short: "Citation", label: "Issue with citation",
      hint: "e.g. wrong paper, theorem number, authors, venue or link" },
    { short: "Correctness", label: "Issue with correctness",
      hint: "e.g. the result is wrong, superseded, or needs an assumption that is missing" },
    { short: "Other", label: "Other issue", hint: "Anything else" },
  ];
  const MAX_URL = 8000;   // GitHub rejects much longer links to its new-issue page

  // Link to a new issue in the atlas repository: the first of the bodies (longest first) whose link GitHub
  // accepts, or null if none does.
  function newIssueUrl(title, ...bodies) {
    for (const body of bodies) {
      const url = `https://github.com/${REPO}/issues/new?title=${encodeURIComponent(title)}&body=${encodeURIComponent(body)}`;
      if (url.length <= MAX_URL) return url;
    }
    return null;
  }

  // Open the issue link in a new tab, with a fallback link in `status` in case the tab is blocked.
  function openIssue(url, status) {
    if (!url) { status.textContent = "The text is too long for a GitHub link. Please shorten it."; return; }
    window.open(url, "_blank", "noopener");
    status.replaceChildren("GitHub opens in a new tab. If it does not, ",
      el("a", { href: url, target: "_blank", rel: "noopener", text: "open the issue here" }), ".");
  }

  const REPORT_NOTE = "This opens a new issue on GitHub, filled in with what you entered here. You can still edit it "
    + "there; nothing is sent until you submit it on GitHub (which needs a GitHub account).";

  // Link to a new issue about an entry, with the reporter's notes and the entry's data.
  // `info`: { kind ("results" or "papers"), id, kindName, title, details: [markdown lines], yaml }.
  function issueUrl(info, chosen) {
    const title = `[${chosen.map((t) => t.topic.short).join(", ")}] ${info.title}`;
    const file = `data/${info.kind}/${info.id}.yaml`;
    const head = [
      `**${info.kindName}:** \`${info.id}\` — ${info.title}`,
      ...info.details,
      `**On the atlas:** ${location.origin}${location.pathname}#${info.id}`,
      `**Data file:** https://github.com/${REPO}/blob/main/${file}`,
    ].join("  \n");
    const body = (yaml) => [
      head,
      ...chosen.map((t) => `### ${t.topic.label}\n\n${t.text}`),
      yaml ? `<details>\n<summary>Current entry (${file})</summary>\n\n\`\`\`yaml\n${yaml}\`\`\`\n\n</details>`
        : "_The current entry is too long to include here; see the data file above._",
    ].join("\n\n");
    return newIssueUrl(title, body(info.yaml), body(null));
  }

  // The report form: one checkbox per topic (several can be chosen), each with its own text field.
  function reportForm(info, close) {
    const topics = REPORT_TOPICS.map((topic) => {
      const box = el("input", { type: "checkbox", value: topic.short.toLowerCase() });
      const text = el("textarea", { rows: "3", placeholder: topic.hint, "aria-label": `${topic.label}: details`, hidden: "" });
      box.addEventListener("change", () => {
        text.hidden = !box.checked;
        if (box.checked) text.focus();
      });
      return { topic, box, text, node: el("div", { class: "report-topic" }, [el("label", {}, [box, topic.label]), text]) };
    });
    const status = el("p", { class: "bib-status", "aria-live": "polite" });
    const submit = el("button", { type: "submit", class: "bib-save", text: "Open GitHub issue ↗" });
    const cancel = el("button", { type: "button", class: "bib-cancel", text: "Cancel" });
    cancel.addEventListener("click", close);

    const form = el("form", { class: "bib-form report-form" }, [
      el("fieldset", {}, [el("legend", { text: `What is wrong with ${info.what}? Select all that apply.` }),
        ...topics.map((t) => t.node)]),
      el("p", { class: "report-note", text: REPORT_NOTE }),
      el("div", { class: "bib-actions" }, [submit, cancel, status]),
    ]);

    form.addEventListener("submit", (e) => {
      e.preventDefault();
      const chosen = topics.filter((t) => t.box.checked);
      if (!chosen.length) { status.textContent = "Select at least one option."; topics[0].box.focus(); return; }
      const empty = chosen.find((t) => !t.text.value.trim());
      if (empty) { status.textContent = `Describe the ${empty.topic.label.toLowerCase()} in its text field.`; empty.text.focus(); return; }
      openIssue(issueUrl(info, chosen.map((t) => ({ topic: t.topic, text: t.text.value.trim() }))), status);
    });
    return { form, focus: () => topics[0].box.focus() };
  }

  // The form behind "Report missing algorithm / lower bound": a link to the paper (required), and optionally
  // the reference in the paper, the runtime, the model and comments.
  function missingForm(problem, bound, close) {
    const noun = bound === "lower" ? "lower bound" : "algorithm";
    const name = problemInfo(problem).name;
    const link = el("input", { type: "url", required: "", placeholder: "https://arxiv.org/abs/… or https://doi.org/…" });
    const reference = el("input", { placeholder: "e.g. Theorem 1.3" });
    const runtime = el("input", { placeholder: bound === "lower" ? "e.g. Ω(log* n)" : "e.g. O(log Δ + log* n)" });
    const model = el("select", {}, options([["", "Not specified"], ["LOCAL", "LOCAL"], ["CONGEST", "CONGEST"],
                                            ["other", "Other (see comments)"]], ""));
    const comments = el("textarea", { rows: "3",
      placeholder: "e.g. randomized, only for trees, needs an assumption on Δ" });
    const status = el("p", { class: "bib-status", "aria-live": "polite" });
    const submit = el("button", { type: "submit", class: "bib-save", text: "Open GitHub issue ↗" });
    const cancel = el("button", { type: "button", class: "bib-cancel", text: "Cancel" });
    cancel.addEventListener("click", close);

    const form = el("form", { class: "bib-form report-form missing-form", novalidate: "" }, [
      el("p", { class: "missing-heading", text: `Report a missing ${noun} for ${name}` }),
      field("Link to the paper (required)", link),
      el("div", { class: "missing-pair" }, [field("Reference in the paper", reference), field("Runtime", runtime)]),
      field("Model", model),
      field("Comments", comments),
      el("p", { class: "report-note", text: REPORT_NOTE }),
      el("div", { class: "bib-actions" }, [submit, cancel, status]),
    ]);

    form.addEventListener("submit", (e) => {
      e.preventDefault();
      const url = link.value.trim();
      let ok = false;
      try { ok = /^https?:$/.test(new URL(url).protocol); } catch (err) { ok = false; }
      if (!ok) { status.textContent = "Enter the link to the paper (starting with https://)."; link.focus(); return; }
      const val = (x) => x.value.trim();
      const modelText = model.value === "other" ? "Other (see comments)" : model.value;
      const title = `[Missing ${noun}] ${name}${val(runtime) ? `: ${val(runtime)}` : ""}`;
      const body = [
        [
          `**Problem:** ${name} (${location.origin}${location.pathname})`,
          `**Missing:** ${noun}`,
          `**Paper:** ${url}`,
          ...(val(reference) ? [`**Reference in the paper:** ${val(reference)}`] : []),
          ...(val(runtime) ? [`**Runtime:** ${val(runtime)}`] : []),
          ...(modelText ? [`**Model:** ${modelText}`] : []),
        ].join("  \n"),
        ...(val(comments) ? [`### Comments\n\n${val(comments)}`] : []),
      ].join("\n\n");
      openIssue(newIssueUrl(title, body), status);
    });
    return { form, focus: () => link.focus() };
  }

  // The data a report about result r carries.
  function resultReportInfo(r) {
    const sources = (r.sources || []).map((s) => {
      const p = data.papers[s.paper];
      return [p ? `${p.label}, “${p.title}”` : s.paper, s.reference].filter(Boolean).join(", ");
    });
    const first = r.sources && r.sources[0] && data.papers[r.sources[0].paper];
    return {
      kind: "results", id: r.id, kindName: "Result", what: "this result", yaml: toYaml(r),
      title: first ? `${r.title} (${first.label})` : r.title,
      details: [
        `**Problem:** ${problemInfo(r.problem).name} · ${r.bound === "lower" ? "lower bound" : "algorithm"}`
          + ` · ${r.model} · ${r.randomness} · ${GRAPH_CLASSES[r.graph_class] || humanize(r.graph_class)}`,
        `**Runtime:** $${r.runtime.latex}$`,
        ...(sources.length ? [`**Source:** ${sources.join("; ")}`] : []),
      ],
    };
  }

  // Open (or close) the report form for result r in a table row below its row `tr`.
  function toggleResultReport(r, tr, btn) {
    const next = tr.nextElementSibling;
    if (next && next.classList.contains("edit-row")) {
      next.remove();
      btn.setAttribute("aria-expanded", "false");
      return;
    }
    btn.setAttribute("aria-expanded", "true");
    const close = () => { row.remove(); btn.setAttribute("aria-expanded", "false"); btn.focus(); };
    const { form, focus } = reportForm(resultReportInfo(r), close);
    form.classList.add("result-form");
    const row = el("tr", { class: "edit-row" }, [el("td", { colspan: String(tr.children.length) }, [form])]);
    tr.after(row);
    focus();
  }

  // ---------- year timeline ----------

  // A to-scale timeline with a dot for every year in `years` (sorted, distinct) and two handles that snap
  // to those years. Drag a handle, click the track (moves the nearer handle), or use the arrow keys.
  // onChange(lo, hi) is called whenever the range changes.
  function buildTimeline(container, valueEl, years, onChange) {
    // The axis runs to the current year (ending in an arrow); the handles stay on years with results.
    const first = years[0], lastResult = years[years.length - 1];
    const last = Math.max(lastResult, new Date().getFullYear());
    const pos = (y) => `${(100 * (y - first)) / (last - first)}%`;
    let lo = first, hi = lastResult;

    const range = el("div", { class: "timeline-range" });
    const dots = years.map((y) => {
      const dot = el("span", { class: "timeline-dot", title: String(y) });
      dot.style.left = pos(y);
      return dot;
    });
    // Axis labels at round years, to scale (every decade, or every 5 years for short spans).
    const step = last - first > 25 ? 10 : 5;
    const axis = [];
    for (let y = Math.ceil(first / step) * step; y <= last; y += step) {
      const tick = el("span", { class: "timeline-axis", text: String(y) });
      tick.style.left = pos(y);
      axis.push(tick);
    }
    const thumb = (which) => el("span", {
      class: `timeline-thumb timeline-thumb-${which}`, role: "slider", tabindex: "0",
      "aria-label": which === "lo" ? "Earliest year" : "Latest year",
      "aria-valuemin": String(first), "aria-valuemax": String(last),
    });
    const loThumb = thumb("lo"), hiThumb = thumb("hi");
    container.replaceChildren(el("div", { class: "timeline-track" }), range, ...axis, ...dots, loThumb, hiThumb);

    function update(notify) {
      loThumb.style.left = pos(lo);
      hiThumb.style.left = pos(hi);
      range.style.left = pos(lo);
      range.style.width = `${(100 * (hi - lo)) / (last - first)}%`;
      loThumb.setAttribute("aria-valuenow", String(lo));
      hiThumb.setAttribute("aria-valuenow", String(hi));
      years.forEach((y, i) => dots[i].classList.toggle("in-range", y >= lo && y <= hi));
      valueEl.textContent = lo === hi ? String(lo) : `${lo} – ${hi}`;
      if (notify) onChange(lo, hi);
    }
    function set(which, year) {
      const next = which === "lo" ? Math.min(year, hi) : Math.max(year, lo);
      if ((which === "lo" ? lo : hi) === next) return;
      if (which === "lo") lo = next; else hi = next;
      update(true);
    }
    // The year closest to a horizontal position in the timeline.
    function yearAt(clientX) {
      const rect = container.getBoundingClientRect();
      const y = first + ((clientX - rect.left) / rect.width) * (last - first);
      return years.reduce((best, x) => (Math.abs(x - y) < Math.abs(best - y) ? x : best), years[0]);
    }
    for (const [which, t] of [["lo", loThumb], ["hi", hiThumb]]) {
      t.addEventListener("pointerdown", (e) => {
        e.preventDefault();
        t.setPointerCapture(e.pointerId);
        t.classList.add("dragging");
        const move = (ev) => set(which, yearAt(ev.clientX));
        const up = () => {
          t.classList.remove("dragging");
          t.removeEventListener("pointermove", move);
          t.removeEventListener("pointerup", up);
        };
        t.addEventListener("pointermove", move);
        t.addEventListener("pointerup", up);
      });
      t.addEventListener("keydown", (e) => {
        const i = years.indexOf(which === "lo" ? lo : hi);
        const target = { ArrowLeft: i - 1, ArrowDown: i - 1, ArrowRight: i + 1, ArrowUp: i + 1,
                         Home: 0, End: years.length - 1 }[e.key];
        if (target === undefined) return;
        e.preventDefault();
        set(which, years[Math.max(0, Math.min(years.length - 1, target))]);
      });
    }
    container.addEventListener("pointerdown", (e) => {
      if (e.target.classList.contains("timeline-thumb")) return;
      const y = yearAt(e.clientX);
      set(Math.abs(y - lo) <= Math.abs(y - hi) && !(y > hi) ? "lo" : "hi", y);
    });
    update(false);
    return {
      reset() { lo = first; hi = lastResult; update(false); onChange(lo, hi); },
    };
  }

  // ---------- landing page ----------

  function setupLanding() {
    const plural = (n, word) => `${n} ${word}${n === 1 ? "" : "s"}`;
    for (const node of document.querySelectorAll("[data-count]")) {
      const results = data.results.filter((r) => r.problem === node.dataset.count);
      const lower = results.filter((r) => r.bound === "lower").length;
      const parts = [plural(results.length - lower, "algorithm")];
      if (lower) parts.push(plural(lower, "lower bound"));
      node.textContent = parts.join(" · ");
    }
  }

  // ---------- problem page ----------

  function setupProblem() {
    const STOPS = [null, ...A.REGIMES.filter((r) => r.slider)];   // index 0: Delta arbitrary
    // The filters start out with all graph classes, all colors and all years, and per table with the randomness
    // and model in DEFAULTS. Algorithms start deterministic (the randomness filter is exact for them); lower
    // bounds start with the setting that lists all of them.
    // Results that rely on assumptions are always listed; the assumptions show in the Graph class column.
    const DEFAULTS = {
      upper: { randomness: "deterministic", model: "LOCAL", graphClass: "all" },   // LOCAL also lists CONGEST algorithms
      lower: { randomness: "deterministic", model: "CONGEST", graphClass: "all" }, // also lists randomized / LOCAL bounds
    };
    const state = {
      bound: "upper",                   // table shown: "upper" (algorithms) or "lower" (lower bounds)
      ...DEFAULTS.upper, sort: "year-desc", stop: 0,
      colors: null,                     // COLOR_TREE id, for coloring problems
      colorsExact: false,               // false: at most that palette; true: exactly that palette
      onlyBest: false,                  // hide results that are not state of the art under the filters
      diameter: "all",                  // network decomposition: "all" or "strong" diameter only
      yearLo: -Infinity, yearHi: Infinity,   // year range of the shown (and compared) results
    };

    const hasColors = data.results.some((r) => r.problem === PROBLEM && r.colors);
    // Network decomposition: runtimes depend on n only, and a result has colors and a cluster diameter.
    // There is no Delta slider; a result is state of the art if no other result is at least as good in
    // runtime, colors, diameter and diameter type at once (and better in one of them).
    const hasDecomp = data.results.some((r) => r.problem === PROBLEM && r.decomposition);
    const CONST = A.REGIMES.find((g) => g.id === "const");
    const decompTerms = new Map();
    for (const r of data.results.filter((x) => x.problem === PROBLEM && x.decomposition)) {
      decompTerms.set(r.id, {
        colors: A.simplify(r.decomposition.colors.expr, CONST),
        diameter: A.simplify(r.decomposition.diameter.expr, CONST),
      });
    }

    // Growth class of a result's number of colors, read off at Delta = n.
    const atN = A.REGIMES.find((g) => g.id === "n");
    const linear = A.simplify("Delta", atN).term;
    const groupCache = new Map();
    function colorGroup(r) {
      if (!r.colors) return null;
      if (!groupCache.has(r.id)) {
        const s = A.simplify(r.colors.expr, atN);
        let id;
        if (s.error) id = "exp";                                // only exponentials in Delta fail here
        else if (s.term.v.every((x) => Math.abs(x) < 1e-9)) id = "const";
        else if (A.compare(s.term, linear) <= 0) id = "linear";
        else id = "poly";
        groupCache.set(r.id, id);
      }
      return groupCache.get(r.id);
    }

    // The most specific COLOR_TREE node of a result: an exact-count leaf if one matches, else its growth class.
    function colorNode(r) {
      if (!r.colors) return null;
      const exact = COLOR_TREE.find((n) => (n.keys || []).includes(colorsKey(r)));
      if (exact) return exact.id;
      const group = colorGroup(r);
      if (COLOR_FALLBACK[group]) return COLOR_FALLBACK[group];
      return COLOR_NODE[group] ? group : "all";
    }

    // Does the colors option `id` include result r (r's node is `id` or below it)?
    function inColorOption(r, id) {
      if (id === null || id === "all") return true;
      // Walk up the tree from r's node; an option with `includes` also contains those nodes' subtrees.
      const seen = new Set();
      const stack = [colorNode(r)];
      while (stack.length) {
        const n = stack.pop();
        if (!n || seen.has(n)) continue;
        if (n === id) return true;
        seen.add(n);
        stack.push(COLOR_NODE[n].parent);
        for (const m of COLOR_TREE) if ((m.includes || []).includes(n)) stack.push(m.id);
      }
      return false;
    }

    function classAndAncestors(c) {
      const out = new Set([c]);
      const stack = [c];
      while (stack.length) for (const p of CLASS_PARENTS[stack.pop()] || []) if (!out.has(p)) { out.add(p); stack.push(p); }
      return out;
    }

    // Does result s also hold in the setting of result r? An algorithm carries over to stronger models
    // (CONGEST -> LOCAL), to randomized algorithms and to subclasses; a lower bound the other way round:
    // to weaker models (LOCAL -> CONGEST), to deterministic algorithms and to superclasses.
    function appliesTo(s, r) {
      if (s.problem !== r.problem || s.bound !== r.bound || colorsKey(s) !== colorsKey(r)) return false;
      const [from, to] = r.bound === "lower" ? [r, s] : [s, r];
      return RANDOMNESS_RANK[from.randomness] <= RANDOMNESS_RANK[to.randomness]
        && MODEL_RANK[from.model] <= MODEL_RANK[to.model]
        && classAndAncestors(to.graph_class).has(from.graph_class)
        && (from.assumptions || []).every((a) => assumptionClosure(to.assumptions).has(a));
    }

    // Filters show every result of the current table that holds in the chosen setting (see appliesTo).
    const isLower = () => state.bound === "lower";
    // Algorithms: exactly the chosen kind. Lower bounds: every bound that holds for it (randomized ones also
    // hold for deterministic algorithms).
    const randomnessMatch = (r, v) => (isLower() ? RANDOMNESS_RANK[r.randomness] >= RANDOMNESS_RANK[v]
      : r.randomness === v);
    const modelMatch = (r, v) => (isLower() ? MODEL_RANK[r.model] >= MODEL_RANK[v] : MODEL_RANK[r.model] <= MODEL_RANK[v]);
    // Graph classes are exact in both tables: "General graphs" lists only results stated for general graphs.
    const classMatch = (r, c) => r.graph_class === c;

    const results = data.results.filter((r) => r.problem === PROBLEM);

    // result id -> regime id -> {term, latex} | {error} | {na}. Also holds each regime shifted up and down by a
    // lower-order factor (ids "<id>+" and "<id>-", see Asymptotics.shifted), used to place crossovers.
    const SHIFTED = A.REGIMES.flatMap((g) => [1, -1].map((dir) => ({ base: g, regime: A.shifted(g, dir) })))
      .filter((s) => s.regime);
    const simplified = new Map();
    for (const r of results) {
      const allowed = allowedRegimes(r);
      const m = new Map();
      for (const g of A.REGIMES) {
        m.set(g.id, allowed && !allowed.includes(g.id) ? { na: true } : A.simplify(r.runtime.expr, g));
      }
      for (const { base, regime } of SHIFTED) {
        m.set(regime.id, allowed && !allowed.includes(base.id) ? { na: true } : A.simplify(r.runtime.expr, regime));
      }
      simplified.set(r.id, m);
    }
    const usable = (s) => !s.error && !s.na;

    // result id -> Set of regime ids where no applicable result *among the filtered results* is strictly
    // faster. Recomputed on every render, so the state of the art always fits the active filters.
    let bestIn = new Map();

    // Pareto version for network decomposition: r is state of the art unless some applicable s is at least
    // as good in runtime, colors and diameter (strong diameter counting as at least as good as weak),
    // and strictly better in one of them.
    function computeParetoBest(pool) {
      const cmp = (a, b) => (a && b && usable(a) && usable(b) ? A.compare(a.term, b.term) : null);
      const best = new Map();
      for (const r of pool) {
        const mine = { runtime: simplified.get(r.id).get(CONST.id), ...decompTerms.get(r.id) };
        const dominated = pool.some((s) => {
          if (s === r || !appliesTo(s, r)) return false;
          if (s.decomposition.diameter_type === "weak" && r.decomposition.diameter_type === "strong") return false;
          const theirs = { runtime: simplified.get(s.id).get(CONST.id), ...decompTerms.get(s.id) };
          const diffs = ["runtime", "colors", "diameter"].map((k) => cmp(theirs[k], mine[k]));
          if (diffs.some((d) => d === null || d > 0)) return false;
          const strongerType = s.decomposition.diameter_type === "strong" && r.decomposition.diameter_type === "weak";
          return diffs.some((d) => d < 0) || strongerType;
        });
        best.set(r.id, new Set(r.bound === "upper" && r.graph_class === "general" && !dominated ? ["pareto"] : []));
      }
      return best;
    }

    // The setting a listed result is judged in: the model and randomness the filters choose (e.g. a CONGEST
    // algorithm listed under LOCAL competes with LOCAL algorithms). Algorithms keep their own graph class (only
    // those for general graphs are ranked); lower bounds are judged for the chosen class, or for general graphs
    // when all classes are shown, so that e.g. a bound for cycles competes with one for trees.
    function settingOf(r) {
      const graph_class = r.bound === "lower" ? (state.graphClass === "all" ? "general" : state.graphClass) : r.graph_class;
      return { ...r, graph_class, model: state.model, randomness: state.randomness };
    }

    const TRIVIAL = A.simplify("1", CONST).term;
    // Compare two terms ignoring the polylog factor an O~ hides (e.g. O~(log^{5/3} n) vs O(log^{5/3} n) tie).
    const compareLead = (a, b) => {
      for (let i = 0; i < a.v.length; i++) {
        if (a.v[i] > b.v[i] + 1e-9) return 1;
        if (a.v[i] < b.v[i] - 1e-9) return -1;
      }
      return 0;
    };
    // result id -> Set of "<regime id>+" / "<regime id>-" where it is beaten but the crossover lies at that
    // regime up to lower-order factors: it is only beaten by an O~ factor there, or it is best once Delta moves
    // up (+) or down (-) by a lower-order factor (e.g. O(log^2 Delta log n) against O(sqrt(Delta)) at
    // Delta = log^2 n). Such a regime bounds its range (bestRanges) when its best range lies on that side, so
    // a crossover at a sampled value of Delta is reported there and not one sample later.
    let nearIn = new Map();

    function computeBest(pool) {
      if (hasDecomp) return computeParetoBest(pool);
      const best = new Map();
      nearIn = new Map();
      for (const r of pool) {
        const set = new Set();
        const near = new Set();
        best.set(r.id, set);
        nearIn.set(r.id, near);
        // Algorithms are only ranked for general graphs; lower bounds for every class, since a bound for a
        // smaller class is a stronger statement.
        if (r.bound === "upper" && r.graph_class !== "general") continue;
        const better = r.bound === "lower" ? 1 : -1;      // a lower bound is better when it is larger
        const setting = settingOf(r);
        for (const g of A.REGIMES) {
          const mine = simplified.get(r.id).get(g.id);
          if (!usable(mine)) continue;
          if (r.bound === "lower" && A.compare(mine.term, TRIVIAL) <= 0) continue;   // Omega(1) says nothing
          const competing = pool.filter((s) => s !== r && appliesTo(s, setting));
          const rivalsAt = (id) => competing.filter((s) => usable(simplified.get(s.id).get(id)))
            .map((s) => simplified.get(s.id).get(id).term);
          const rivals = rivalsAt(g.id);
          if (!rivals.some((t) => A.compare(t, mine.term) === better)) { set.add(g.id); continue; }
          const onlyTilde = !rivals.some((t) => compareLead(t, mine.term) === better);
          for (const id of [`${g.id}+`, `${g.id}-`]) {
            const moved = simplified.get(r.id).get(id);   // undefined for constant Delta, which is not moved
            const bestMoved = moved && usable(moved) && !rivalsAt(id).some((t) => A.compare(t, moved.term) === better);
            if (onlyTilde || bestMoved) near.add(id);
          }
        }
      }
      // Second pass: a result that is best somewhere only through ties (e.g. O(Delta^2 + log* n) next to
      // O(sqrt(Delta) + log* n), which both give log* n for constant Delta) is not state of the art when another
      // applicable result dominates it: at least as good at every sampled Delta where it holds, and better at one.
      // Such a rival is itself best wherever the dominated result is, so it is enough to look for any dominator.
      for (const r of pool) {
        if (!best.get(r.id).size && !nearIn.get(r.id).size) continue;
        const better = r.bound === "lower" ? 1 : -1;
        const setting = settingOf(r);
        const mine = simplified.get(r.id);
        const dominated = pool.some((s) => {
          if (s === r || !appliesTo(s, setting)) return false;
          const theirs = simplified.get(s.id);
          let strict = false;
          for (const g of A.REGIMES) {
            if (!usable(mine.get(g.id))) continue;
            if (!usable(theirs.get(g.id))) return false;     // s does not cover a Delta that r covers
            const c = A.compare(theirs.get(g.id).term, mine.get(g.id).term);
            if (c === -better) return false;
            if (c === better) strict = true;
          }
          return strict;
        });
        if (dominated) {
          best.set(r.id, new Set());
          nearIn.set(r.id, new Set());
        }
      }
      return best;
    }

    // Describe the sampled regimes where a result is best as ranges of Delta.
    function bestRanges(r) {
      const set = bestIn.get(r.id);
      const idx = A.REGIMES.map((g, i) => (set.has(g.id) ? i : -1)).filter((i) => i >= 0);
      if (!idx.length) return [];
      const allowed = allowedRegimes(r);
      const first = allowed ? A.REGIMES.findIndex((g) => allowed.includes(g.id)) : 0;
      const last = allowed ? A.REGIMES.length - 1 - [...A.REGIMES].reverse().findIndex((g) => allowed.includes(g.id)) : A.REGIMES.length - 1;
      const runs = [];
      for (const i of idx) {
        if (runs.length && runs[runs.length - 1][1] === i - 1) runs[runs.length - 1][1] = i;
        else runs.push([i, i]);
      }
      // A neighbouring sample where the result is only behind by an O~ factor is where the crossover lies.
      const near = nearIn.get(r.id) || new Set();
      // The sample below a run counts if the result wins once Delta moves up from it, the sample above if it
      // wins once Delta moves down.
      for (const run of runs) {
        if (run[0] > 0 && near.has(`${A.REGIMES[run[0] - 1].id}+`)) run[0] -= 1;
        if (run[1] < A.REGIMES.length - 1 && near.has(`${A.REGIMES[run[1] + 1].id}-`)) run[1] += 1;
      }
      return runs.map(([a, b]) => {
        const lo = A.REGIMES[a].point, hi = A.REGIMES[b].point;
        if (a === first && b === last) {
          if (!allowed) return "\\text{all } \\Delta";
          return a === b ? `\\Delta = \\Theta(${lo})` : "\\text{all admissible } \\Delta";
        }
        if (a === b) return `\\Delta = \\Theta(${lo})`;
        if (a === 0) return `\\Delta \\lesssim ${hi}`;
        if (b === A.REGIMES.length - 1) return `\\Delta \\gtrsim ${lo}`;
        return `${lo} \\lesssim \\Delta \\lesssim ${hi}`;
      });
    }

    // ---------- table ----------

    function runtimeCell(r, regime) {
      const cell = el("td", { class: "col-runtime" });
      if (!regime) {
        cell.append(runtimeTex(r.runtime.latex));
        return cell;
      }
      const s = simplified.get(r.id).get(regime.id);
      if (s.na) {
        cell.append(runtimeTex(r.runtime.latex), el("span", { class: "sub", text: "Not for this Δ" }));
      } else if (s.error) {
        const text = /diameter/.test(s.error) ? "Depends on the diameter D" : "Could not simplify";
        cell.append(runtimeTex(r.runtime.latex), el("span", { class: "sub", text }));
      } else {
        cell.append(runtimeTex(s.latex));
        const norm = (x) => x.replace(/\s+/g, "").replace(/\\star/g, "*");
        if (norm(s.latex) !== norm(r.runtime.latex)) {
          cell.append(el("span", { class: "sub original" }, [tex(r.runtime.latex)]));
        }
      }
      return cell;
    }

    function bestCell(r) {
      const cell = el("td", { class: "col-best" });
      const ranges = bestRanges(r);
      if (!ranges.length) cell.append(el("span", { class: "none", text: "—" }));
      for (const latex of ranges) cell.append(el("div", {}, [tex(latex)]));
      return cell;
    }

    function isBest(r, regime) {
      const set = bestIn.get(r.id);
      return regime ? set.has(regime.id) : set.size > 0;
    }

    function row(r, regime) {
      const graphClass = el("td", { class: "col-class" }, [GRAPH_CLASSES[r.graph_class] || humanize(r.graph_class)]);
      if (r.assumptions && r.assumptions.length) {
        for (const a of r.assumptions) graphClass.append(el("span", { class: "sub assumption", text: ASSUMPTIONS[a] || humanize(a) }));
      }
      const best = isBest(r, regime);
      const yearCell = el("td", { class: "col-year" }, [String(r.year)]);
      const runtime = runtimeCell(r, regime);
      if (best) runtime.append(el("span", { class: "best-badge", text: "State of the art" }));
      const editBtn = el("button", { type: "button", class: "bib-edit-btn entry-edit", "aria-expanded": "false",
                                     title: "Edit this result", text: "Edit" });
      const reportBtn = el("button", { type: "button", class: "bib-edit-btn entry-report", "aria-expanded": "false",
                                       title: "Report an issue with this result", text: "Report an issue" });
      const tr = el("tr", { id: r.id, class: best ? "is-best" : null }, [
        yearCell,
        runtime,
        ...(hasColors ? [el("td", { class: "col-colors" }, r.colors ? [tex(r.colors.latex)] : [])] : []),
        ...(hasDecomp ? [
          el("td", { class: "col-colors" }, r.decomposition ? [tex(r.decomposition.colors.latex)] : []),
          el("td", { class: "col-diameter" }, r.decomposition ? [
            runtimeTex(r.decomposition.diameter.latex),
            el("span", { class: `sub diameter-${r.decomposition.diameter_type}`, text: r.decomposition.diameter_type }),
          ] : []),
        ] : [bestCell(r)]),
        el("td", { class: "col-model" }, [
          el("span", { class: `chip ${r.randomness}`, text: r.randomness === "deterministic" ? "Det." : "Rand." }),
          el("span", { class: "chip model", text: r.model }),
        ]),
        graphClass,
        sourceCell(r.sources),
        el("td", { class: "col-comments" }, [reductionChips(r), ...(r.comments ? commentNodes(r.comments) : [])].filter(Boolean)),
        el("td", { class: "col-edit" }, [editBtn, reportBtn]),
      ]);
      editBtn.addEventListener("click", () => toggleResultForm(r, tr, editBtn));
      reportBtn.addEventListener("click", () => toggleResultReport(r, tr, reportBtn));
      return tr;
    }

    function sorter(chosen) {
      const regime = chosen || (hasDecomp ? CONST : null);   // decomposition runtimes do not depend on Delta
      if (state.sort === "runtime" && regime) {
        const best = isLower() ? -1 : 1;                   // best first: fastest algorithms, largest lower bounds
        return (a, b) => {
          const sa = simplified.get(a.id).get(regime.id), sb = simplified.get(b.id).get(regime.id);
          if (!usable(sa) || !usable(sb)) return (usable(sa) ? 0 : 1) - (usable(sb) ? 0 : 1) || a.year - b.year;
          return best * A.compare(sa.term, sb.term) || a.year - b.year;
        };
      }
      const dir = state.sort === "year-desc" ? -1 : 1;
      return (a, b) => dir * (a.year - b.year) || a.id.localeCompare(b.id);
    }

    function render() {
      const regime = STOPS[state.stop];
      if (!regime && !hasDecomp && state.sort === "runtime") state.sort = "year-desc";

      // Each filter as a predicate; an option's count applies all *other* filters, so it tells how many
      // results the table would show (or gain) with that option chosen. Options without results are hidden.
      const inGroup = inColorOption;
      const FILTERS = {
        bound: (r) => r.bound === state.bound,
        randomness: (r) => randomnessMatch(r, state.randomness),
        model: (r) => modelMatch(r, state.model),
        colors: (r) => (state.colorsExact ? colorNode(r) === state.colors : inGroup(r, state.colors)),
        classes: (r) => state.graphClass === "all" || classMatch(r, state.graphClass),
        diameter: (r) => state.diameter === "all" || (r.decomposition && r.decomposition.diameter_type === state.diameter),
        years: (r) => r.year >= state.yearLo && r.year <= state.yearHi,
      };
      const segmentValue = (r, key) => (key === "diameter" ? r.decomposition && r.decomposition.diameter_type : r[key]);
      const without = (...skip) => results.filter((r) => Object.entries(FILTERS).every(([k, f]) => skip.includes(k) || f(r)));
      const filtered = without(null);
      bestIn = computeBest(filtered);
      const rows = filtered.filter((r) => !state.onlyBest || isBest(r, regime)).sort(sorter(regime));

      // Options only appear when the active table has results for them. An option without results under the
      // other filters stays visible while it is selected, so the current choice can always be seen and undone.
      const inTable = results.filter((r) => r.bound === state.bound);
      const showOption = (btn, n, matches) => {
        const offered = inTable.some(matches);
        btn.hidden = !offered || (n === 0 && btn.getAttribute("aria-pressed") !== "true");
        const span = btn.querySelector(".pill-count");
        if (span) span.textContent = String(n);
      };
      for (const key of ["randomness", "model", "diameter"]) {
        const pool = without(key);
        for (const btn of section.querySelectorAll(`.segmented[data-key="${key}"] button`)) {
          const v = btn.dataset.value;
          const matches = key === "model" ? (r) => modelMatch(r, v)
            : key === "randomness" ? (r) => randomnessMatch(r, v)
              : (r) => v === "all" || segmentValue(r, key) === v;
          showOption(btn, pool.filter(matches).length, matches);
        }
      }
      const colorPool = without("colors");
      for (const btn of section.querySelectorAll("#colors-filter button")) {
        const id = btn.querySelector(".pill-count").dataset.value;
        const atMost = colorPool.filter((r) => inGroup(r, id)).length;
        const exact = colorPool.filter((r) => colorNode(r) === id).length;
        btn.dataset.exact = String(exact);
        const selected = id === state.colors;
        const single = id === "all" || COLOR_NODE[id].single;
        if (selected && !single) btn.dataset.mode = state.colorsExact ? "exact" : "atmost";
        else delete btn.dataset.mode;
        btn.title = single ? ""
          : selected && state.colorsExact ? "Exactly this palette (click again for at most)"
            : "At most this palette (click again for exactly)";
        showOption(btn, selected && state.colorsExact ? exact : atMost, (r) => inGroup(r, id));
      }
      const classPool = without("classes");
      const classFilter = document.getElementById("class-filter");
      for (const btn of classFilter.querySelectorAll("button:not(.pill-all)")) {
        const c = btn.querySelector(".pill-count").dataset.value;
        btn.setAttribute("aria-pressed", String(state.graphClass === c));
        showOption(btn, classPool.filter((r) => classMatch(r, c)).length, (r) => classMatch(r, c));
        // Lower bounds have no "General graphs" option: the bounds for general graphs are listed under All.
        if (isLower() && c === "general") btn.hidden = true;
      }
      const allClassesBtn = classFilter.querySelector(".pill-all");
      allClassesBtn.setAttribute("aria-pressed", String(state.graphClass === "all"));
      allClassesBtn.querySelector(".pill-count").textContent = String(classPool.length);
      // A filter without any option for this table disappears; so does the year filter for a single year.
      for (const item of filterBar.querySelectorAll(".filter-item[data-options]")) {
        item.hidden = !item.querySelector(".filter-popover button:not(.pill-all):not([hidden])");
      }
      // The graph class filter is also left out when its only option would list the same results as All.
      const classOptions = [...classFilter.querySelectorAll("button:not(.pill-all):not([hidden])")];
      if (state.graphClass === "all" && classOptions.length === 1
          && classPool.every((r) => classMatch(r, classOptions[0].querySelector(".pill-count").dataset.value))) {
        classFilter.closest(".filter-item").hidden = true;
      }
      for (const [bound, t] of Object.entries(timelines)) if (t) t.box.hidden = bound !== state.bound;
      const activeTimeline = timelines[state.bound];
      document.getElementById("years-group").hidden = !activeTimeline;
      if (activeTimeline) document.getElementById("timeline-value").textContent = activeTimeline.value.textContent;
      showFilterValues();

      document.getElementById("results-body").replaceChildren(...rows.map((r) => row(r, regime)));
      const empty = document.getElementById("results-empty");
      empty.hidden = rows.length > 0;
      empty.textContent = inTable.length ? "No results match these filters."
        : `No ${isLower() ? "lower bounds" : "algorithms"} for this problem yet.`;
      filterBar.hidden = !inTable.length;             // nothing to filter in an empty table
      const total = results.filter((r) => r.bound === state.bound).length;
      const noun = isLower() ? (total === 1 ? "lower bound" : "lower bounds") : (total === 1 ? "algorithm" : "algorithms");
      document.getElementById("result-count").textContent =
        rows.length === total ? `${total} ${noun}` : `${rows.length} of ${total} ${noun}`;
      for (const tab of section.querySelectorAll(".bound-tabs [role=tab]")) {
        tab.setAttribute("aria-selected", String(tab.dataset.bound === state.bound));
        tab.querySelector(".pill-count").textContent = String(results.filter((r) => r.bound === tab.dataset.bound).length);
      }
      document.getElementById("missing-label").textContent = `Report missing ${isLower() ? "lower bound" : "algorithm"}`;
      if (missingFor && missingFor !== state.bound) closeMissing();
      const footer = document.getElementById("footer-text");
      if (footer && !hasDecomp) footer.textContent = (isLower() ? FOOTER_LOWER : FOOTER).replace(/\s+/g, " ").trim();

      const yearBtn = document.getElementById("sort-year");
      const runtimeBtn = document.getElementById("sort-runtime");
      document.getElementById("sort-arrow").textContent = state.sort === "year-desc" ? "↓" : "↑";
      yearBtn.classList.toggle("active", state.sort !== "runtime");
      runtimeBtn.classList.toggle("active", state.sort === "runtime");
      runtimeBtn.disabled = !regime && !hasDecomp;
      runtimeBtn.title = hasDecomp ? "Sort by runtime" : regime ? "Sort by runtime in this regime" : "Choose a value of Δ to sort by runtime";
      if (hasDecomp) return;

      document.getElementById("regime-value").replaceChildren(
        regime ? tex(`\\Theta(${regime.point})`) : document.createTextNode("any"));
      const note = document.getElementById("regime-note");
      note.hidden = !regime || !inTable.length;
      note.replaceChildren(...(regime
        ? [document.createTextNode("Runtimes simplified to functions of n. Highlighted: state of the art for "),
           tex(`\\Delta = ${regime.label}`),
           document.createTextNode(".")]
        : []));
      for (const [i, tick] of document.querySelectorAll("#regime-ticks button").entries()) {
        tick.setAttribute("aria-pressed", String(i === state.stop));
      }
    }

    // ---------- wiring ----------

    const timelines = {};             // bound -> {box, value, ctl} | null (see the year filter below)
    const colorStart = { upper: { colors: null, colorsExact: false }, lower: { colors: null, colorsExact: false } };

    const section = document.getElementById("results");
    section.setAttribute("aria-labelledby", "results-title");
    section.innerHTML = RESULTS_TEMPLATE;
    const filterBar = document.getElementById("filter-bar");

    // "Report missing algorithm / lower bound" below the table; shown on the public site only, like "Report an issue".
    const missingBtn = document.getElementById("missing-btn");
    const missingSlot = document.getElementById("missing-slot");
    let missingFor = null;            // the table ("upper" or "lower") the open form is for
    const closeMissing = () => {
      missingSlot.replaceChildren();
      missingFor = null;
      missingBtn.setAttribute("aria-expanded", "false");
    };
    missingBtn.addEventListener("click", () => {
      if (missingFor) { closeMissing(); return; }
      missingFor = state.bound;
      const { form, focus } = missingForm(PROBLEM, state.bound, () => { closeMissing(); missingBtn.focus(); });
      missingSlot.append(form);
      missingBtn.setAttribute("aria-expanded", "true");
      focus();
    });
    // Filters a problem does not have at all are dropped (colors only for colorings, diameter only for decompositions).
    if (!hasColors) document.getElementById("colors-group").remove();
    if (!hasDecomp) document.getElementById("diameter-group").remove();
    if (hasColors) {
      document.getElementById("sort-runtime").closest("th")
        .after(el("th", { scope: "col", text: "Colors" }));
    }
    if (hasDecomp) {
      // No Delta: drop the slider, its note and the "State of the art for" column; add colors and diameter.
      document.getElementById("regime-panel").remove();
      document.getElementById("regime-note").remove();
      document.getElementById("best-col").closest("table").classList.add("decomp-table");
      document.getElementById("best-col").remove();
      document.getElementById("sort-runtime").closest("th")
        .after(el("th", { scope: "col", text: "Colors" }), el("th", { scope: "col", text: "Diameter" }));
      document.getElementById("diameter-group").hidden = false;
    }

    // The current choice of each filter, shown on its toggle.
    function showFilterValues() {
      const set = (id, nodes) => { const x = document.getElementById(id); if (x) x.replaceChildren(...nodes); };
      const text = (t) => [document.createTextNode(t)];
      set("fv-randomness", text(state.randomness === "deterministic" ? "Deterministic" : "Randomized"));
      set("fv-model", text(state.model));
      set("fv-diameter", text(state.diameter === "strong" ? "Strong" : "All"));
      const pressedColors = section.querySelector("#colors-filter button[aria-pressed=true]");
      if (pressedColors) {
        const label = pressedColors.cloneNode(true);
        label.querySelectorAll(".pill-count").forEach((x) => x.remove());
        const mode = pressedColors.dataset.mode === "exact" ? "= " : pressedColors.dataset.mode === "atmost" ? "≤ " : "";
        set("fv-colors", [...(mode ? [document.createTextNode(mode)] : []), ...label.childNodes]);
      }
      set("fv-classes", text(state.graphClass === "all" ? "All"
        : GRAPH_CLASSES[state.graphClass] || humanize(state.graphClass)));
    }


    function closePopovers(except) {
      for (const t of filterBar.querySelectorAll(".filter-toggle")) {
        if (t === except) continue;
        t.setAttribute("aria-expanded", "false");
        document.getElementById(t.getAttribute("aria-controls")).hidden = true;
      }
    }
    filterBar.addEventListener("click", (e) => {
      const t = e.target.closest(".filter-toggle");
      if (!t) return;
      const open = t.getAttribute("aria-expanded") !== "true";
      closePopovers(t);
      t.setAttribute("aria-expanded", String(open));
      const pop = document.getElementById(t.getAttribute("aria-controls"));
      pop.hidden = !open;
      if (open) {                                         // keep the popover inside the viewport
        pop.style.left = "";
        const over = pop.getBoundingClientRect().right - (document.documentElement.clientWidth - 16);
        if (over > 0) pop.style.left = `${-Math.min(over, pop.parentElement.getBoundingClientRect().left - 16)}px`;
      }
    });
    document.addEventListener("click", (e) => { if (!e.target.closest(".filter-item")) closePopovers(); });
    document.addEventListener("keydown", (e) => {
      if (e.key !== "Escape") return;
      const open = filterBar.querySelector(".filter-toggle[aria-expanded=true]");
      closePopovers();
      if (open) open.focus();
    });

    const slider = document.getElementById("regime-slider");
    if (slider) {
    slider.max = String(STOPS.length - 1);
    const ticks = document.getElementById("regime-ticks");
    STOPS.forEach((g, i) => {
      const btn = el("button", { type: "button", "aria-pressed": "false" },
        [g ? tex(g.label) : document.createTextNode("any")]);
      btn.style.setProperty("--pos", `${(100 * i) / (STOPS.length - 1)}%`);
      btn.addEventListener("click", () => { state.stop = i; slider.value = String(i); render(); });
      ticks.append(btn);
    });
    slider.addEventListener("input", () => { state.stop = Number(slider.value); render(); });
    }

    // Colors: the options of the problem's COLOR_TREE in one row, in tree order (each option right before
    // the options it contains; siblings by `order`, else most results first).
    if (hasColors) {
      const total = (id) => results.filter((r) => inColorOption(r, id)).length;
      const colorButtons = [];
      const filterRow = document.getElementById("colors-filter");
      const build = (node) => {
        const btn = el("button", { type: "button" }, [
          node.latex ? tex(node.latex) : node.label, el("span", { class: "pill-count", "data-value": node.id }),
        ]);
        // First click: "at most" this palette (this option and everything below it). Clicking the selected
        // option again cycles to "exactly" this palette and back (skipping "exactly" when it has no results).
        btn.addEventListener("click", () => {
          if (state.colors === node.id) {
            const exactAvailable = node.id !== "all" && !node.single && Number(btn.dataset.exact) > 0;
            state.colorsExact = !state.colorsExact && exactAvailable;
          } else {
            state.colors = node.id;
            state.colorsExact = false;
          }
          for (const b of colorButtons) b.setAttribute("aria-pressed", String(b === btn));
          render();
        });
        colorButtons.push(btn);
        filterRow.append(btn);
        COLOR_TREE.filter((c) => c.parent === node.id && total(c.id) > 0)
          .sort((a, b) => (a.order ?? 99) - (b.order ?? 99) || total(b.id) - total(a.id))
          .forEach(build);
      };
      build(COLOR_NODE.all);
      // Algorithms start at the problem's initial palette if there are results for it (vertex coloring: exactly
      // Delta + 1), else at All; lower bounds always start at All.
      const initial = (COLOR_TREES[PROBLEM] || {}).initial;
      for (const bound of ["upper", "lower"]) {
        const use = bound === "upper" && initial && results.some((r) => r.bound === bound && colorNode(r) === initial.id);
        colorStart[bound] = use ? { colors: initial.id, colorsExact: Boolean(initial.exact) } : { colors: "all", colorsExact: false };
      }
      Object.assign(state, colorStart.upper);
      for (const b of colorButtons) {
        b.setAttribute("aria-pressed", String(b.querySelector(".pill-count").dataset.value === state.colors));
      }
      document.getElementById("colors-group").hidden = false;
    }

    // Graph classes: "All" (the default) or exactly one class. One option per class that occurs in this
    // problem's results, in vocabulary order; which of them are pressed or shown is decided in render().
    function classPills(container, occurring) {
      const values = Object.keys(GRAPH_CLASSES).filter((v) => occurring.has(v));
      for (const v of occurring) if (!values.includes(v)) values.push(v);
      const pick = (v) => { state.graphClass = v; render(); };
      const allBtn = el("button", { type: "button", class: "pill-all", "aria-pressed": "true" }, [
        "All", el("span", { class: "pill-count", "data-value": ALL_CLASSES }),
      ]);
      allBtn.addEventListener("click", () => pick("all"));
      container.append(allBtn);
      for (const v of values) {
        const btn = el("button", { type: "button", "aria-pressed": "false" }, [
          GRAPH_CLASSES[v] || humanize(v),
          el("span", { class: "pill-count", "data-value": v }),
        ]);
        btn.addEventListener("click", () => pick(v));
        container.append(btn);
      }
    }
    classPills(document.getElementById("class-filter"), new Set(results.map((r) => r.graph_class)));

    // Years: only results from the chosen range are shown and compared for the state of the art.
    // Years: one timeline per table, with the years that table has results in; each keeps its own range.
    // Only results from the chosen range are shown and compared for the state of the art.
    const yearRange = {};
    for (const bound of ["upper", "lower"]) {
      const years = [...new Set(results.filter((r) => r.bound === bound).map((r) => r.year))].sort((a, b) => a - b);
      if (years.length < 2) { timelines[bound] = null; continue; }
      const box = el("div", { class: "timeline" });
      const value = el("span");
      document.getElementById("timelines").append(box);
      const ctl = buildTimeline(box, value, years, (lo, hi) => {
        yearRange[bound] = { lo, hi };
        if (state.bound === bound) { state.yearLo = lo; state.yearHi = hi; render(); }
      });
      timelines[bound] = { box, value, ctl };
    }
    const useYearRange = () => {
      const range = yearRange[state.bound];
      state.yearLo = range ? range.lo : -Infinity;
      state.yearHi = range ? range.hi : Infinity;
    };

    for (const seg of section.querySelectorAll(".segmented[data-key]")) {
      seg.addEventListener("click", (e) => {
        const btn = e.target.closest("button");
        if (!btn) return;
        state[seg.dataset.key] = btn.dataset.value;
        for (const b of seg.querySelectorAll("button")) b.setAttribute("aria-pressed", String(b === btn));
        render();
      });
    }

    const savedChoice = { upper: { ...DEFAULTS.upper, ...colorStart.upper }, lower: { ...DEFAULTS.lower, ...colorStart.lower } };
    for (const tab of section.querySelectorAll(".bound-tabs [role=tab]")) {
      // Each table keeps its own randomness, model and graph class choice.
      tab.addEventListener("click", () => {
        if (tab.dataset.bound === state.bound) return;
        savedChoice[state.bound] = { randomness: state.randomness, model: state.model, graphClass: state.graphClass,
                                     colors: state.colors, colorsExact: state.colorsExact };
        state.bound = tab.dataset.bound;
        useYearRange();
        for (const [key, value] of Object.entries(savedChoice[state.bound])) {
          state[key] = value;
          for (const b of section.querySelectorAll(`.segmented[data-key="${key}"] button`)) {
            b.setAttribute("aria-pressed", String(b.dataset.value === value));
          }
        }
        for (const b of section.querySelectorAll("#colors-filter button")) {
          b.setAttribute("aria-pressed", String(b.querySelector(".pill-count").dataset.value === state.colors));
        }
        render();
      });
    }

    document.getElementById("only-best").addEventListener("change", (e) => {
      state.onlyBest = e.target.checked;
      render();
    });

    document.getElementById("sort-year").addEventListener("click", () => {
      state.sort = state.sort === "year-desc" ? "year-asc" : "year-desc";
      render();
    });
    document.getElementById("sort-runtime").addEventListener("click", () => {
      state.sort = "runtime";
      render();
    });

    render();

    // After saving a result the page reloads at #<result id>: widen the filters if they hide it, then show it.
    const wanted = location.hash && results.find((x) => x.id === decodeURIComponent(location.hash.slice(1)));
    if (wanted && !document.getElementById(wanted.id)) {
      const press = (seg, value) => {
        state[seg] = value;
        for (const b of section.querySelectorAll(`.segmented[data-key="${seg}"] button`)) {
          b.setAttribute("aria-pressed", String(b.dataset.value === value));
        }
      };
      state.bound = wanted.bound;
      press("randomness", wanted.bound === "lower" ? "deterministic" : wanted.randomness);
      if (timelines[state.bound]) timelines[state.bound].ctl.reset();
      useYearRange();
      press("model", wanted.bound === "lower" ? "CONGEST" : "LOCAL");   // the setting that lists them all
      if (hasDecomp) press("diameter", "all");
      if (hasColors) {
        state.colors = "all";
        state.colorsExact = false;
        for (const b of section.querySelectorAll("#colors-filter button")) {
          b.setAttribute("aria-pressed", String(b.querySelector(".pill-count").dataset.value === "all"));
        }
      }
      state.graphClass = "all";
      state.onlyBest = false;
      document.getElementById("only-best").checked = false;
      render();
    }
    const target = wanted && document.getElementById(wanted.id);
    if (target && target.closest("#results-body")) {
      target.classList.add("is-target");
      target.scrollIntoView({ block: "center" });
    }
  }

  // ---------- reductions ----------

  const INSTANCE_GRAPHS = {
    same: { name: "Input graph", latex: "G", short: null },
    "line-graph": { name: "Line graph", latex: "L(G)", short: "L(G)" },
    "clique-product": { name: "Product", latex: "G \\times K_{\\Delta+1}", short: "G × K" },
    components: { name: "Remaining components", latex: "C \\subseteq G", short: null },
  };

  function reductionName(r) {
    return `${problemInfo(r.from.problem).name} → ${problemInfo(r.to.problem).name}`;
  }

  // Diagram: the four symmetry-breaking problems in the corners, network decomposition in the middle.
  const MAP_NODES = {
    "maximal-matching": [110, 50], mis: [470, 50],
    "edge-coloring": [110, 290], "vertex-coloring": [470, 290],
    "network-decomposition": [290, 170],
  };
  const SVG_NS = "http://www.w3.org/2000/svg";

  function svg(tag, attrs, children) {
    const node = document.createElementNS(SVG_NS, tag);
    for (const [k, v] of Object.entries(attrs || {})) {
      if (k === "text") node.textContent = v;
      else node.setAttribute(k, v);
    }
    for (const c of children || []) node.append(c);
    return node;
  }

  function drawReductionMap(root, reductions) {
    const size = {};
    const nodes = svg("g", { class: "map-nodes" });
    for (const [id, [x, y]] of Object.entries(MAP_NODES)) {
      const p = problemInfo(id);
      const w = p.name.length * 9.2 + 30, h = 42;
      size[id] = [w, h];
      const box = svg("g", { class: "map-node" }, [
        svg("rect", { x: x - w / 2, y: y - h / 2, width: w, height: h, rx: 8 }),
        svg("text", { x, y: y + 6, "text-anchor": "middle", text: p.name }),
      ]);
      nodes.append(p.page ? svg("a", { href: p.page }, [box]) : box);
    }

    // One arrow per (from, to) pair; arrows in both directions are drawn side by side.
    const pairs = new Map();
    for (const r of reductions) {
      const key = `${r.from.problem}>${r.to.problem}`;
      if (!pairs.has(key)) pairs.set(key, []);
      pairs.get(key).push(r);
    }
    const arrows = svg("g", { class: "map-arrows" });
    for (const [key, list] of pairs) {
      const [from, to] = key.split(">");
      if (!MAP_NODES[from] || !MAP_NODES[to]) continue;
      if (from === to) {
        // Reduction within one problem (e.g. shattering): a loop on the outer side of the box (left for boxes
        // on the left half of the map, right for the others), away from the arrows between problems.
        const [x, y] = MAP_NODES[from], [w, h] = size[from];
        const side = x < 290 ? -1 : 1;
        const sx = x + side * (w / 2 - 8), sy = y + h / 2 + 2, ex = x + side * (w / 2 + 2), ey = y + h / 2 - 12;
        const d = `M${sx},${sy} C${sx + side * 4},${sy + 46} ${ex + side * 40},${ey + 30} ${ex + side * 4},${ey}`;
        arrows.append(svg("a", { href: `#${list[0].id}`, class: "map-arrow", "data-from": from, "data-to": to }, [
          svg("title", { text: list.map((r) => `${reductionName(r)}: ${r.title}`).join("\n") }),
          svg("path", { d, class: "hit", fill: "none" }),
          svg("path", { d, class: "shaft", fill: "none", "marker-end": "url(#map-head)" }),
        ]));
        continue;
      }
      const [x1, y1] = MAP_NODES[from], [x2, y2] = MAP_NODES[to];
      const len = Math.hypot(x2 - x1, y2 - y1), dx = (x2 - x1) / len, dy = (y2 - y1) / len;
      const nx = -dy, ny = dx;                                   // left-hand normal
      const shift = pairs.has(`${to}>${from}`) ? 9 : 0;
      // Distance from a box centre to its border along the arrow.
      const exit = ([w, h]) => Math.min(w / 2 / Math.abs(dx || 1e-9), h / 2 / Math.abs(dy || 1e-9));
      const a = exit(size[from]) + 4, b = exit(size[to]) + 8;
      const sx = x1 + dx * a + nx * shift, sy = y1 + dy * a + ny * shift;
      const ex = x2 - dx * b + nx * shift, ey = y2 - dy * b + ny * shift;
      const title = list.map((r) => `${reductionName(r)}: ${r.title}`).join("\n");
      const group = svg("a", { href: `#${list[0].id}`, class: "map-arrow", "data-from": from, "data-to": to }, [
        svg("title", { text: title }),
        svg("line", { x1: sx, y1: sy, x2: ex, y2: ey, class: "hit" }),
        svg("line", { x1: sx, y1: sy, x2: ex, y2: ey, class: "shaft", "marker-end": "url(#map-head)" }),
      ]);
      const label = INSTANCE_GRAPHS[list[0].instance.graph];
      if (label && label.short) {
        const off = shift + 16;
        const lx = (sx + ex) / 2 + nx * off, ly = (sy + ey) / 2 + ny * off;
        const anchor = Math.abs(nx) < 0.3 ? "middle" : nx > 0 ? "start" : "end";
        const text = svg("text", { x: lx, y: ly + 5, "text-anchor": anchor, class: "map-label" }, [label.short]);
        if (list[0].instance.graph === "clique-product") {
          text.append(svg("tspan", { "baseline-shift": "sub", "font-size": "0.75em", text: "Δ+1" }));
        }
        group.append(text);
      }
      arrows.append(group);
    }
    root.replaceChildren(
      svg("defs", {}, [svg("marker", {
        id: "map-head", viewBox: "0 0 10 10", refX: "8", refY: "5",
        markerWidth: "7", markerHeight: "7", orient: "auto-start-reverse",
      }, [svg("path", { d: "M0,0 L10,5 L0,10 z" })])]),
      arrows, nodes);
  }

  function setupReductions() {
    const reductions = data.reductions || [];

    function problemCell(p) {
      const cell = el("td", { class: "col-problem" }, [problemLink(p.problem)]);
      if (p.colors) cell.append(el("span", { class: "sub" }, [tex(`${p.colors.latex} \\text{ colors}`)]));
      return cell;
    }

    function instanceCell(r) {
      const g = INSTANCE_GRAPHS[r.instance.graph] || { name: humanize(r.instance.graph), latex: "" };
      const cell = el("td", { class: "col-instance" }, [
        el("span", {}, [`${g.name} `, tex(g.latex)]),
      ]);
      if (r.instance.graph !== "same") {
        cell.append(
          el("span", { class: "sub" }, [tex(`n' = ${r.instance.n.latex}`)]),
          el("span", { class: "sub" }, [tex(`\\Delta' = ${r.instance.Delta.latex}`)]),
        );
      }
      if (r.graph_class) {
        cell.append(el("span", { class: "sub", text: `Only on ${(GRAPH_CLASSES[r.graph_class] || humanize(r.graph_class)).toLowerCase()}` }));
      }
      return cell;
    }

    const rows = reductions.map((r) => el("tr", { id: r.id }, [
      problemCell(r.from),
      el("td", { class: "col-with" }, [tex("T")]),
      problemCell(r.to),
      el("td", { class: "col-runtime" }, [runtimeTex(r.runtime.latex)]),
      instanceCell(r),
      el("td", { class: "col-model" }, [
        ...modelChips(r.models),
        ...(r.randomness === "randomized" ? [el("span", { class: "chip randomized", text: "Rand." })] : []),
      ]),
      sourceCell(r.sources),
      el("td", { class: "col-technique" }, [
        el("span", { class: "technique", text: r.title }),
        ...(r.comments ? [el("span", { class: "sub" }, commentNodes(r.comments))] : []),
      ]),
    ]));
    document.getElementById("reductions-body").replaceChildren(...rows);
    const map = document.getElementById("reduction-map");
    drawReductionMap(map, reductions);
    renderMath(document.querySelector(".illustration figcaption"));

    // Problem filter: show the reductions from or to one problem (single choice).
    let selected = "all";
    const involves = (r, p) => p === "all" || r.from.problem === p || r.to.problem === p;
    const filter = document.getElementById("reduction-filter");
    const occurring = new Set(reductions.flatMap((r) => [r.from.problem, r.to.problem]));
    const options = ["all", ...Object.keys(PROBLEMS).filter((p) => occurring.has(p)),
      ...[...occurring].filter((p) => !PROBLEMS[p])];
    const buttons = options.map((p) => {
      const n = reductions.filter((r) => involves(r, p)).length;
      const btn = el("button", { type: "button", "aria-pressed": String(p === selected) }, [
        p === "all" ? "All" : problemInfo(p).name,
        el("span", { class: "pill-count", text: String(n) }),
      ]);
      btn.addEventListener("click", () => { selected = p; render(); });
      filter.append(btn);
      return btn;
    });

    function render() {
      buttons.forEach((b, i) => b.setAttribute("aria-pressed", String(options[i] === selected)));
      let shown = 0;
      reductions.forEach((r, i) => {
        const on = involves(r, selected);
        rows[i].hidden = !on;
        if (on) shown += 1;
      });
      for (const a of map.querySelectorAll(".map-arrow")) {
        a.classList.toggle("is-dim", selected !== "all" && a.dataset.from !== selected && a.dataset.to !== selected);
      }
      const total = reductions.length;
      document.getElementById("reduction-count").textContent = shown === total
        ? (total === 1 ? "1 reduction" : `${total} reductions`)
        : `${shown} of ${total} reductions`;
    }
    render();
  }

  // ---------- bibliography ----------

  function joinAuthors(names) {
    if (names.length <= 2) return names.join(" and ");
    return `${names.slice(0, -1).join(", ")} and ${names[names.length - 1]}`;
  }

  function setupBibliography() {
    const byPaper = new Map();
    const add = (entry, sources, key) => {
      for (const s of sources || []) {
        if (!byPaper.has(s.paper)) byPaper.set(s.paper, []);
        byPaper.get(s.paper).push({ [key]: entry, reference: s.reference });
      }
    };
    for (const r of data.results) add(r, r.sources, "result");
    for (const r of data.reductions || []) add(r, r.sources, "reduction");
    const papers = [...byPaper.keys()].map((id) => data.papers[id]).filter(Boolean)
      .sort((a, b) => a.sort_key.localeCompare(b.sort_key));

    // Readable names for the hosts that public_url links usually point to.
    const HOSTS = {
      "arxiv.org": "arXiv", "dl.acm.org": "ACM DL", "ieeexplore.ieee.org": "IEEE Xplore",
      "www.sciencedirect.com": "ScienceDirect", "link.springer.com": "Springer",
      "epubs.siam.org": "SIAM", "drops.dagstuhl.de": "LIPIcs", "doi.org": "DOI",
    };

    // Name of the link to the public version: the publisher or archive, else "PDF" for other PDFs.
    function publicLinkText(url) {
      try {
        const u = new URL(url);
        return HOSTS[u.hostname] || (/\.pdf$/i.test(u.pathname) ? "PDF" : u.hostname);
      } catch (e) {
        return "Paper";
      }
    }

    // The versions (venue and year, as plain text), followed by the one link to the public version.
    function versionLine(paper) {
      const line = el("p", { class: "bib-venues" });
      paper.versions.forEach((v, i) => {
        if (i > 0) line.append(document.createTextNode(" · "));
        line.append(el("span", { title: v.venue_name, text: `${v.venue} ${v.year}` }));
        if (v.title) line.append(el("span", { class: "bib-alt-title", text: ` (as “${v.title}”)` }));
      });
      if (paper.public_url) {
        line.append(document.createTextNode(" · "),
          el("a", { class: "bib-public", href: paper.public_url, target: "_blank", rel: "noopener",
                    text: `${publicLinkText(paper.public_url)} ↗` }));
      }
      return line;
    }

    function reductionItem({ reduction: r, reference }) {
      return el("li", { class: "bib-result" }, [
        el("span", { class: "bib-result-kind", text: "Reduction" }),
        el("span", { class: "bib-result-problem" }, [
          el("a", { href: `reductions.html#${r.id}`, text: reductionName(r) }),
        ]),
        el("span", { class: "bib-result-runtime" }, [tex(r.runtime.latex)]),
        el("span", { class: "bib-result-model" }, modelChips(r.models)),
        el("span", { class: "bib-result-meta", text: [r.title, reference].filter(Boolean).join(" · ") }),
      ]);
    }

    function resultItem({ result: r, reference }) {
      const name = problemLink(r.problem);
      const classText = GRAPH_CLASSES[r.graph_class] || humanize(r.graph_class);
      const extras = [classText, ...(r.assumptions || []).map((a) => ASSUMPTIONS[a] || humanize(a)), reference]
        .filter(Boolean).join(" · ");
      return el("li", { class: "bib-result" }, [
        el("span", { class: "bib-result-kind", text: r.bound === "lower" ? "Lower bound for" : "Algorithm for" }),
        el("span", { class: "bib-result-problem" }, [name]),
        el("span", { class: "bib-result-runtime" }, [tex(r.runtime.latex)]),
        el("span", { class: "bib-result-model" }, [
          el("span", { class: `chip ${r.randomness}`, text: r.randomness === "deterministic" ? "Det." : "Rand." }),
          el("span", { class: "chip model", text: r.model }),
        ]),
        el("span", { class: "bib-result-meta", text: extras }),
      ]);
    }

    // ---------- editing a paper ----------
    // With scripts/serve.py the form saves to data/papers/<id>.yaml; otherwise it shows the YAML to copy.

    const authorChoices = Object.entries(data.authors || {}).sort((a, b) => a[1].localeCompare(b[1]));
    const venueChoices = (type) => Object.entries(data.venues || {})
      .filter(([, v]) => !type || v.type === type)
      .map(([id, v]) => [id, v.short_name ? `${v.short_name} (${v.name})` : v.name])
      .sort((a, b) => a[1].localeCompare(b[1]));

    function authorRow(id) {
      const row = el("div", { class: "bib-row bib-author-row" });
      row.append(el("select", { "aria-label": "Author" }, options(authorChoices, id)), removeButton(row));
      return row;
    }
    function versionRow(v) {
      const row = el("div", { class: "bib-row bib-version-row" });
      const type = el("select", { "data-k": "type", "aria-label": "Type" },
        options([["conference", "Conference"], ["journal", "Journal"], ["preprint", "Preprint"], ["book", "Book"]], v.type || "conference"));
      const venue = el("select", { "data-k": "venue", "aria-label": "Venue" });
      const fillVenues = () => venue.replaceChildren(...options(venueChoices(type.value), v.venue));
      type.addEventListener("change", () => { v.venue = venue.value; fillVenues(); });
      fillVenues();
      const input = (k, label, attrs) => el("input", { "data-k": k, "aria-label": label, placeholder: label,
                                                      value: v[k] ?? "", ...attrs });
      row.append(type, venue, input("year", "Year", { type: "number", min: "1900", max: "2100", class: "bib-year" }),
        input("title", "Title if different"), input("doi", "DOI"), input("arxiv", "arXiv id"), input("url", "URL"),
        removeButton(row));
      return row;
    }

    function toggleEditForm(paper, body, btn) {
      const open = body.querySelector(".bib-form");
      if (open) { open.remove(); btn.setAttribute("aria-expanded", "false"); return; }
      btn.setAttribute("aria-expanded", "true");
      const raw = paper.raw || {};
      const text = (name, value, attrs) => el("input", { name, value: value ?? "", ...attrs });
      const label = text("label", raw.label), title = text("title", raw.title);
      const url = text("public_url", raw.public_url, { type: "url", placeholder: "https://…" });
      const authors = el("div", { class: "bib-rows" }, (raw.authors || []).map(authorRow));
      const versions = el("div", { class: "bib-rows" }, (raw.versions || []).map((v) => versionRow({ ...v })));
      const addAuthor = el("button", { type: "button", class: "bib-add", text: "+ Author" });
      addAuthor.addEventListener("click", () => authors.append(authorRow(authorChoices[0][0])));
      const addVersion = el("button", { type: "button", class: "bib-add", text: "+ Version" });
      addVersion.addEventListener("click", () => versions.append(versionRow({ type: "conference" })));
      const status = el("p", { class: "bib-status", "aria-live": "polite" });
      const yamlBox = el("pre", { class: "bib-yaml", hidden: "" });
      const save = el("button", { type: "submit", class: "bib-save", text: editable ? "Save" : "Show YAML" });
      const cancel = el("button", { type: "button", class: "bib-cancel", text: "Cancel" });
      cancel.addEventListener("click", () => { form.remove(); btn.setAttribute("aria-expanded", "false"); });

      const form = el("form", { class: "bib-form" }, [
        el("div", { class: "bib-grid" }, [field("Label", label), field("Title", title), field("Public URL", url)]),
        el("fieldset", {}, [el("legend", { text: "Authors" }), authors, addAuthor]),
        el("fieldset", {}, [el("legend", { text: "Versions" }), versions, addVersion]),
        el("div", { class: "bib-actions" }, [save, cancel, status]),
        yamlBox,
      ]);
      form.addEventListener("submit", async (e) => {
        e.preventDefault();
        const out = {
          id: paper.id, label: label.value.trim(), title: title.value.trim(),
          authors: [...authors.querySelectorAll("select")].map((s) => s.value),
        };
        if (url.value.trim()) out.public_url = url.value.trim();
        out.versions = [...versions.querySelectorAll(".bib-version-row")].map((row) => {
          const v = {};
          for (const inp of row.querySelectorAll("[data-k]")) {
            const val = inp.value.trim();
            if (val) v[inp.dataset.k] = inp.dataset.k === "year" ? Number(val) : val;
          }
          return v;
        });
        await saveEntry("papers", paper.id, out, status, yamlBox, paper.id);
      });
      body.append(form);
      label.focus();
    }

    // Open (or close) the report form for a paper below its entry.
    function togglePaperReport(paper, body, btn) {
      const open = body.querySelector(".bib-form");
      if (open) { open.remove(); btn.setAttribute("aria-expanded", "false"); return; }
      btn.setAttribute("aria-expanded", "true");
      const venues = paper.versions.map((v) => `${v.venue} ${v.year}`).join(" · ");
      const info = {
        kind: "papers", id: paper.id, kindName: "Paper", what: "this paper's entry", yaml: toYaml(paper.raw || {}),
        title: `${paper.label}: ${paper.title}`,
        details: [
          `**Authors:** ${joinAuthors(paper.authors)}`,
          ...(venues ? [`**Versions:** ${venues}`] : []),
          ...(paper.public_url ? [`**Link:** ${paper.public_url}`] : []),
        ],
      };
      const { form, focus } = reportForm(info, () => { form.remove(); btn.setAttribute("aria-expanded", "false"); btn.focus(); });
      body.append(form);
      focus();
    }

    const list = document.getElementById("bib-list");
    for (const paper of papers) {
      const entries = byPaper.get(paper.id);
      const results = entries.filter((e) => e.result)
        .sort((a, b) => a.result.problem.localeCompare(b.result.problem) || a.result.year - b.result.year);
      const reductions = entries.filter((e) => e.reduction);
      const count = (k, word) => (k === 0 ? null : k === 1 ? `1 ${word}` : `${k} ${word}s`);
      const titleNode = paper.public_url
        ? el("a", { href: paper.public_url, target: "_blank", rel: "noopener", text: paper.title })
        : el("span", { text: paper.title });
      const details = el("details", { class: "bib-results" }, [
        el("summary", {}, [
          el("span", { text: [count(results.length, "result"), count(reductions.length, "reduction")]
            .filter(Boolean).join(" · ") }),
          el("span", { class: "chevron", "aria-hidden": "true" }),
        ]),
        el("ul", {}, [...results.map(resultItem), ...reductions.map(reductionItem)]),
      ]);
      const body = el("div", { class: "bib-body" }, [
        el("p", { class: "bib-authors", text: joinAuthors(paper.authors) }),
        el("p", { class: "bib-title" }, [titleNode]),
        versionLine(paper),
        details,
      ]);
      const editBtn = el("button", { type: "button", class: "bib-edit-btn entry-edit", "aria-expanded": "false",
                                     title: "Edit this paper's entry", text: "Edit" });
      editBtn.addEventListener("click", () => toggleEditForm(paper, body, editBtn));
      const reportBtn = el("button", { type: "button", class: "bib-edit-btn entry-report", "aria-expanded": "false",
                                       title: "Report an issue with this paper's entry", text: "Report an issue" });
      reportBtn.addEventListener("click", () => togglePaperReport(paper, body, reportBtn));
      list.append(el("li", { class: "bib-entry", id: paper.id }, [
        el("div", { class: "bib-side" }, [el("span", { class: "bib-label", text: paper.label }), editBtn, reportBtn]),
        body,
      ]));
    }

    document.getElementById("bib-count").textContent =
      `${papers.length} papers with at least one result or reduction in the database, sorted by first author.`;

    const toggle = document.getElementById("toggle-all");
    const panels = () => [...list.querySelectorAll("details.bib-results")];
    const syncToggle = () => {
      const allOpen = panels().every((d) => d.open);
      toggle.textContent = allOpen ? "Collapse all" : "Expand all";
      toggle.setAttribute("aria-pressed", String(allOpen));
    };
    toggle.addEventListener("click", () => {
      const open = !panels().every((d) => d.open);
      for (const d of panels()) d.open = open;
      syncToggle();
    });
    list.addEventListener("toggle", syncToggle, true);

    // A link to bibliography.html#paper-id opens that paper's panel.
    const target = location.hash && document.getElementById(decodeURIComponent(location.hash.slice(1)));
    if (target) {
      const d = target.querySelector("details");
      if (d) d.open = true;
      target.classList.add("is-target");
      target.scrollIntoView();
    }
  }

  // ---------- start ----------

  renderMath(document.getElementById("problem-text"));
  renderMath(document.querySelector(".illustration figcaption"));
  const footer = document.getElementById("footer-text");
  if (footer && PROBLEM) {
    footer.textContent = (PROBLEM === "network-decomposition" ? FOOTER_DECOMPOSITION : FOOTER).replace(/\s+/g, " ").trim();
  }
  if (PROBLEM) setupProblem();
  else if (document.body.dataset.page === "bibliography") setupBibliography();
  else if (document.body.dataset.page === "reductions") setupReductions();
  else setupLanding();
})();
