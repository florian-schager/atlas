/*
 * Asymptotic engine for runtime expressions.
 *
 * Parses the machine-readable `expr` strings of results (e.g. "O(log(Delta)^2 * log(n))"),
 * substitutes a regime for Delta, and reduces the result to a single dominant term in n.
 *
 * A term is a product of growth factors, kept as an exponent vector ordered from the
 * fastest-growing scale to the slowest:
 *
 *   [ n^c, n^(i/k), 2^(log^e n · loglog^f n), log n, 2^(loglog^e n · logloglog^f n), log log n, ...,
 *     2^(log* n), log* n, log log* n ]
 *
 * (the exponential factor at each level has two exponents e and f, so that bounds like
 * 2^O(sqrt(log n · log log n)) are representable).
 *
 * Within this family any two terms are comparable by comparing the vectors
 * lexicographically, so a sum always reduces to its largest term.
 * Õ(f) is modelled as f times an unknown polylog(f) factor, which counts as larger than
 * any fixed power of the next-slower scale.
 */
(function (global) {
  "use strict";

  const LEVELS = 5;                   // iterated logs tracked: log n ... log^(5) n
  const C = 0;                        // exponent of n (constant part)
  const IK = 1;                       // exponent of n in units of 1/k (k an arbitrary constant)
  const X = (k) => 3 * k - 1;         // 2^((log^(k) n)^e · ...): exponent e
  const XP = (k) => 3 * k;            //   ... · (log^(k+1) n)^f): exponent f
  const L = (k) => 3 * k + 1;         // (log^(k) n)^e
  const XSTAR = 3 * LEVELS + 2;       // 2^(e · log* n): above every power of log* n, below every iterated log
  const LSTAR = XSTAR + 1;            // log* n
  const LLSTAR = LSTAR + 1;           // log log* n
  const SIZE = LLSTAR + 1;
  const POLY = 1e6;                   // stands for "some polylog factor" in comparisons
  const EPS = 1e-9;

  // Classify a vector index: {kind: "n" | "X" | "XP" | "L" | "star", k}.
  function slot(i) {
    if (i === C || i === IK) return { kind: "n", k: 0 };
    if (i === XSTAR) return { kind: "xstar", k: 0 };
    if (i === LSTAR) return { kind: "star", k: 0 };
    if (i === LLSTAR) return { kind: "llstar", k: 0 };
    const k = Math.floor((i - 2) / 3) + 1;
    return { kind: ["X", "XP", "L"][(i - 2) % 3], k };
  }

  // ---------- terms ----------

  function term(entries) {
    const v = new Array(SIZE).fill(0);
    for (const [i, e] of entries || []) v[i] = e;
    return { v, poly: -1 };
  }

  function lead(t) {
    for (let i = 0; i < SIZE; i++) if (Math.abs(t.v[i]) > EPS) return i;
    return -1;
  }

  function vec(t) {
    const v = t.v.slice();
    if (t.poly >= 0) v[t.poly] += POLY;
    return v;
  }

  function compare(a, b) {
    const va = vec(a), vb = vec(b);
    for (let i = 0; i < SIZE; i++) {
      if (va[i] > vb[i] + EPS) return 1;
      if (va[i] < vb[i] - EPS) return -1;
    }
    return 0;
  }

  function minPoly(p, q) {
    if (p < 0) return q;
    if (q < 0) return p;
    return Math.min(p, q);
  }

  function mul(a, b) {
    const t = term();
    for (let i = 0; i < SIZE; i++) t.v[i] = a.v[i] + b.v[i];
    t.poly = minPoly(a.poly, b.poly);
    return t;
  }

  function powNum(a, r) {
    const t = term();
    for (let i = 0; i < SIZE; i++) t.v[i] = a.v[i] * r;
    t.poly = a.poly;
    return t;
  }

  function max(a, b) {
    return compare(a, b) >= 0 ? a : b;
  }

  // log of a term is Theta(log of its dominant factor).
  function log(a) {
    const i = lead(a);
    if (i < 0) return term();
    const { kind, k } = slot(i);
    if (kind === "n") return term([[L(1), 1]]);
    if (kind === "star") return term([[LLSTAR, 1]]);
    if (kind === "xstar") return term([[LSTAR, a.v[XSTAR]]]);
    // log(log log* n) grows slower than every scale tracked here; it is treated as a constant, which only rounds
    // up a runtime that divides by it.
    if (kind === "llstar") return term();
    if (k >= LEVELS) throw new Error("too many nested logarithms");
    // 2^((log^(k) n)^e · (log^(k+1) n)^f)  ->  (log^(k) n)^e · (log^(k+1) n)^f
    if (kind === "X") return term([[L(k), a.v[X(k)]], [L(k + 1), a.v[XP(k)]]]);
    if (kind === "XP") return term([[L(k + 1), a.v[XP(k)]]]);
    return term([[L(k + 1), 1]]);     // log^(k) n  ->  log^(k+1) n
  }

  function logstar(a) {
    return lead(a) < 0 ? term() : term([[LSTAR, 1]]);
  }

  // b^a for a constant b > 1: same growth class as 2^a.
  // Supported exponents: (log^(k) n)^e with e < 1, optionally times (log^(k+1) n)^f; log^(k) n; and
  // (log^(k) n)^e with e > 1 for k >= 2.
  function exp2(a) {
    const i = lead(a);
    if (i < 0) return term();
    const { kind, k } = slot(i);
    // 2^(e · log* n), e.g. 10^(log* (1/eps)).
    if (kind === "star" && a.poly < 0 && !a.v.some((x, j) => j !== i && Math.abs(x) > EPS)) return term([[XSTAR, a.v[i]]]);
    if (kind !== "L" || a.poly >= 0) throw new Error("unsupported exponential");
    const e = a.v[i];
    const f = k < LEVELS ? a.v[L(k + 1)] : 0;
    const others = a.v.some((x, j) => j !== i && (k >= LEVELS || j !== L(k + 1)) && Math.abs(x) > EPS);
    if (others) throw new Error("unsupported exponential");
    if (e < 1 - EPS) return term([[X(k), e], [XP(k), f]]);
    if (Math.abs(e - 1) < EPS && Math.abs(f) < EPS) return k === 1 ? term([[C, 1]]) : term([[L(k - 1), 1]]);
    // 2^((log^(k) n)^e) with e > 1, e.g. 2^(log^2 log Delta): faster than every power of log^(k-1) n but slower
    // than 2^((log^(k-1) n)^eps). That is the second exponent of the exponential one level up, with the first at 0.
    if (e > 1 + EPS && Math.abs(f) < EPS && k >= 2) return term([[XP(k - 1), e]]);
    throw new Error("unsupported exponential");
  }

  // Õ(f): f times polylog(f), i.e. a polynomial factor on the next-slower scale.
  function tilde(a) {
    const i = lead(a);
    let p = -1;
    if (i >= 0) {
      const { kind, k } = slot(i);
      if (kind === "n") p = L(1);
      else if (kind === "X" || kind === "XP") p = L(k);
      else if (kind === "L" && k < LEVELS) p = L(k + 1);
      else if (kind === "star") p = LLSTAR;
      else if (kind === "xstar") p = LSTAR;
    }
    const t = powNum(a, 1);
    t.poly = minPoly(a.poly, p);
    return t;
  }

  // ---------- parser ----------

  function tokenize(src) {
    const re = /\s*(?:(\d+(?:\.\d+)?)|([A-Za-z_]\w*)|(.))/gy;
    const out = [];
    let m;
    while (re.lastIndex < src.length && (m = re.exec(src))) {
      if (m[1]) out.push({ t: "num", v: parseFloat(m[1]) });
      else if (m[2]) out.push({ t: "id", v: m[2] });
      else if (m[3] && m[3].trim()) out.push({ t: "op", v: m[3] });
    }
    return out;
  }

  function parse(src) {
    const toks = tokenize(src);
    let pos = 0;
    const peek = () => toks[pos];
    const isOp = (v) => peek() && peek().t === "op" && peek().v === v;
    const expect = (v) => {
      if (!isOp(v)) throw new Error(`expected '${v}' in ${src}`);
      pos++;
    };

    function expr() {
      let node = product();
      while (isOp("+") || isOp("-")) {
        const op = toks[pos++].v;
        node = { type: "bin", op, l: node, r: product() };
      }
      return node;
    }
    function product() {
      let node = power();
      while (isOp("*") || isOp("/")) {
        const op = toks[pos++].v;
        node = { type: "bin", op, l: node, r: power() };
      }
      return node;
    }
    function power() {
      const base = atom();
      if (isOp("^")) { pos++; return { type: "bin", op: "^", l: base, r: power() }; }
      return base;
    }
    function atom() {
      const tok = toks[pos++];
      if (!tok) throw new Error(`unexpected end of ${src}`);
      if (tok.t === "num") return { type: "num", value: tok.v };
      if (tok.t === "op" && tok.v === "(") { const e = expr(); expect(")"); return e; }
      if (tok.t === "id") {
        if (isOp("(")) {
          pos++;
          const args = [expr()];
          while (isOp(",")) { pos++; args.push(expr()); }   // several arguments only for min(...)
          expect(")");
          if (args.length > 1 && tok.v !== "min") throw new Error(`${tok.v} takes one argument in ${src}`);
          return { type: "call", name: tok.v, arg: args[0], args };
        }
        return { type: "var", name: tok.v };
      }
      throw new Error(`unexpected '${tok.v}' in ${src}`);
    }

    const ast = expr();
    if (pos !== toks.length) throw new Error(`trailing input in ${src}`);
    return ast;
  }

  // ---------- evaluation ----------

  const num = (x) => ({ num: true, x });
  const FIXED = 65536;                // value of n and Delta when only the dependence on eps is wanted
  const CONSTANTS = { eps: 0.1, delta: 0.1, gamma: 0.1, lambda: 2 };
  const asTerm = (val) => (val.num ? term() : val);

  function evaluate(node, env) {
    switch (node.type) {
      case "num":
        return num(node.value);
      case "var":
        // The dependence on eps for fixed n and Delta (see epsDependence): eps = 1/x for a growing x.
        if (env.eps) {
          if (node.name === "n" || node.name === "Delta") return num(FIXED);
          if (node.name === "eps") return powNum(term([[C, 1]]), -1);
        }
        if (node.name === "n") return term([[C, 1]]);
        if (node.name === "Delta") {
          if (!env.delta) throw new Error("no regime for Delta");
          return env.delta;
        }
        // Fixed (small) constants of a result, e.g. the eps in (1+eps)Delta colors.
        if (CONSTANTS[node.name] !== undefined) return num(CONSTANTS[node.name]);
        // The diameter D is independent of n and Delta, so a runtime in terms of D has no value in a regime.
        if (node.name === "D") throw new Error("depends on the diameter D");
        throw new Error(`unknown variable ${node.name}`);
      case "call": {
        if (node.name === "min") {                       // min(f, g, ...): the slowest-growing argument
          const vals = node.args.map((x) => evaluate(x, env));
          if (vals.every((v) => v.num)) return num(Math.min(...vals.map((v) => v.x)));
          return vals.map(asTerm).reduce((p, q) => (compare(p, q) <= 0 ? p : q));
        }
        const a = evaluate(node.arg, env);
        switch (node.name) {
          case "O": case "Theta": case "Omega": return a;
          case "Otilde": return a.num ? a : tilde(a);
          case "log": return a.num ? num(Math.log2(a.x)) : log(a);
          case "logstar": return a.num ? num(1) : logstar(a);
          case "sqrt": return a.num ? num(Math.sqrt(a.x)) : powNum(a, 0.5);
          // poly(f): f to an unspecified constant power; only known when f is constant.
          case "poly":
            if (a.num || lead(a) < 0) return num(1);
            throw new Error("unspecified polynomial");
          default: throw new Error(`unknown function ${node.name}`);
        }
      }
      case "bin": {
        const a = evaluate(node.l, env), b = evaluate(node.r, env);
        if (a.num && b.num) {
          const ops = { "+": a.x + b.x, "-": a.x - b.x, "*": a.x * b.x, "/": a.x / b.x, "^": Math.pow(a.x, b.x) };
          return num(ops[node.op]);
        }
        switch (node.op) {
          case "+": return max(asTerm(a), asTerm(b));
          case "-":                                       // f - g = Theta(f) when g grows strictly slower
            if (!a.num && (b.num || compare(a, b) > 0)) return a;
            throw new Error("unsupported difference");
          case "*": return mul(asTerm(a), asTerm(b));
          case "/":
            if (b.num) return a;
            return mul(asTerm(a), powNum(b, -1));        // negative exponents, e.g. log^3 n / log Delta
          case "^":
            if (b.num) return powNum(a, b.x);
            if (a.num && a.x > 1) return exp2(b);
            if (!a.num) return exp2(mul(b, log(a)));      // f^g = 2^(g log f), e.g. Delta^(2 Delta + 1)
            throw new Error("unsupported power");
        }
      }
    }
    throw new Error("bad expression");
  }

  // ---------- LaTeX output ----------

  function frac(x) {
    for (let d = 1; d <= 12; d++) {
      const nmr = Math.round(x * d);
      if (Math.abs(x * d - nmr) < 1e-6) return d === 1 ? String(nmr) : `${nmr}/${d}`;
    }
    return String(Math.round(x * 100) / 100);
  }

  function logLatex(k, e) {
    const base = ["", "\\log n", "\\log\\log n", "\\log\\log\\log n"][k] || `\\log^{(${k})} n`;
    if (Math.abs(e - 1) < EPS) return base;
    if (Math.abs(e - 0.5) < EPS) return `\\sqrt{${base}}`;
    if (k === 1) return `\\log^{${frac(e)}} n`;
    if (k === 2) return `\\log^{${frac(e)}}\\log n`;
    return `(${base})^{${frac(e)}}`;
  }

  function nLatex(c, ik) {
    let exp;
    if (Math.abs(ik) < EPS) exp = frac(c);
    else {
      const kPart = Math.abs(ik - 1) < EPS ? "1/k" : `${frac(ik)}/k`;
      exp = Math.abs(c) < EPS ? kPart : `${frac(c)} + ${kPart}`;
    }
    return exp === "1" ? "n" : `n^{${exp}}`;
  }

  function toLatex(t, wrap) {
    const v = t.v;
    const parts = [];
    const below = [];                 // factors with negative exponents go into a denominator
    const put = (e, render) => {
      if (e > EPS) parts.push(render(e));
      else if (e < -EPS) below.push(render(-e));
    };
    if (Math.abs(v[C]) > EPS || Math.abs(v[IK]) > EPS) parts.push(nLatex(v[C], v[IK]));
    let onlyExp = true;
    for (let k = 1; k <= LEVELS; k++) {
      const e = v[X(k)], f = v[XP(k)];
      if (Math.abs(e) > EPS || Math.abs(f) > EPS) {
        let inner;
        if (Math.abs(e - 0.5) < EPS && Math.abs(f - 0.5) < EPS) {
          inner = `\\sqrt{${logLatex(k, 1)} \\cdot ${logLatex(k + 1, 1)}}`;
        } else {
          inner = [Math.abs(e) > EPS ? logLatex(k, e) : null, Math.abs(f) > EPS ? logLatex(k + 1, f) : null]
            .filter(Boolean).join(" \\cdot ");
        }
        parts.push(`2^{\\mathcal{O}(${inner})}`);
      }
      if (Math.abs(v[L(k)]) > EPS) { put(v[L(k)], (x) => logLatex(k, x)); onlyExp = false; }
    }
    if (Math.abs(v[XSTAR]) > EPS) put(v[XSTAR], () => "2^{\\mathcal{O}(\\log^{*} n)}");
    if (Math.abs(v[LSTAR]) > EPS) {
      put(v[LSTAR], (x) => (Math.abs(x - 1) < EPS ? "\\log^{*} n" : `(\\log^{*} n)^{${frac(x)}}`));
      onlyExp = false;
    }
    if (Math.abs(v[LLSTAR]) > EPS) {
      put(v[LLSTAR], (x) => (Math.abs(x - 1) < EPS ? "\\log\\log^{*} n" : `(\\log\\log^{*} n)^{${frac(x)}}`));
      onlyExp = false;
    }
    if (Math.abs(v[C]) > EPS || Math.abs(v[IK]) > EPS) onlyExp = false;
    const hasExp = parts.length > 0 && onlyExp && !below.length;
    if (hasExp && parts.length === 1 && t.poly < 0) return parts[0];
    const top = parts.length ? parts.join(" \\cdot ") : "1";
    const inner = below.length ? `\\frac{${top}}{${below.join(" \\cdot ")}}` : top;
    const op = t.poly >= 0 ? "\\widetilde{\\mathcal{O}}"
      : wrap === "Omega" ? "\\Omega" : wrap === "Theta" ? "\\Theta" : "\\mathcal{O}";
    return `${op}(${inner})`;
  }

  // ---------- regimes for Delta ----------

  // Ordered by growth of Delta. `slider` marks the regimes offered in the UI;
  // the others are extra sample points used to decide where a result is best.
  const REGIMES = [
    { id: "const", slider: true, label: "\\Theta(1)", point: "1", delta: term() },
    { id: "logstar", point: "\\log^{*} n", delta: term([[LSTAR, 1]]) },
    { id: "loglog", slider: true, label: "\\Theta(\\log\\log n)", point: "\\log\\log n", delta: term([[L(2), 1]]) },
    // log Delta = log log n / log log log n: where bounds like log Delta and log log n / log log log n cross.
    { id: "exploglog", point: "2^{\\log\\log n / \\log\\log\\log n}", delta: term([[X(2), 1], [XP(2), -1]]) },
    { id: "sqrtlog", point: "\\sqrt{\\log n}", delta: term([[L(1), 0.5]]) },
    { id: "log", slider: true, label: "\\Theta(\\log n)", point: "\\log n", delta: term([[L(1), 1]]) },
    { id: "log2", point: "\\log^{2} n", delta: term([[L(1), 2]]) },
    { id: "log3", point: "\\log^{3} n", delta: term([[L(1), 3]]) },
    { id: "exp14", point: "2^{\\log^{1/4} n}", delta: term([[X(1), 0.25]]) },
    { id: "exp13", point: "2^{\\log^{1/3} n}", delta: term([[X(1), 1 / 3]]) },
    { id: "exp12", point: "2^{\\sqrt{\\log n}}", delta: term([[X(1), 0.5]]) },
    { id: "exp23", point: "2^{\\log^{2/3} n}", delta: term([[X(1), 2 / 3]]) },
    { id: "nk", slider: true, label: "\\Theta(n^{1/k})", point: "n^{1/k}", delta: term([[IK, 1]]) },
    { id: "n", slider: true, label: "\\Theta(n)", point: "n", delta: term([[C, 1]]) },
  ];

  // A regime moved by a lower-order factor: Delta times (dir = 1) or divided by (dir = -1) a large power of the
  // next-slower scale, e.g. log^2 n -> log^2 n · (log log n)^K. A result that is best there although it is beaten
  // at the regime itself crosses over at the regime up to lower-order factors. Constant Delta is not moved.
  const SHIFT = 1000;
  function shifted(regime, dir) {
    const i = lead(regime.delta);
    if (i < 0) return null;
    const { kind, k } = slot(i);
    let p = -1;
    if (kind === "n" || kind === "X" || kind === "XP") p = L(Math.max(k, 1));
    else if (kind === "L" && k < LEVELS) p = L(k + 1);
    else if (kind === "star") p = LLSTAR;
    if (p < 0) return null;
    return { id: `${regime.id}${dir > 0 ? "+" : "-"}`, delta: mul(regime.delta, term([[p, dir * SHIFT]])) };
  }

  const cache = new Map();
  function parsed(src) {
    if (!cache.has(src)) cache.set(src, parse(src));
    return cache.get(src);
  }

  function wrapOf(ast) {
    return ast.type === "call" && ["O", "Otilde", "Omega", "Theta"].includes(ast.name) ? ast.name : "O";
  }

  /** Simplify an expression under a regime. Returns {term, latex} or {error}. */
  function simplify(src, regime) {
    try {
      const ast = parsed(src);
      const val = evaluate(ast, { delta: regime.delta });
      const t = val.num ? term() : val;
      return { term: t, latex: toLatex(t, wrapOf(ast)) };
    } catch (e) {
      return { error: e.message };
    }
  }

  /**
   * The dependence of an expression on eps, with n and Delta fixed: the growth as eps -> 0, as a term in
   * x = 1/eps (written as n). E.g. O(eps^-1 log n) gives x, O(eps^-1 log(1/eps) log n) gives x log x.
   * Returns {term} or {error}.
   */
  function epsDependence(src) {
    try {
      const val = evaluate(parsed(src), { eps: true });
      return { term: val.num ? term() : val };
    } catch (e) {
      return { error: e.message };
    }
  }

  global.Asymptotics = { REGIMES, simplify, compare, shifted, parse, epsDependence };
})(window);
