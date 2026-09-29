-- Prove2me | Theorems.Thm_markov_brothers_integer_grid_v2
-- name    : markov_brothers_integer_grid_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-05-09T02:17:07.487353+00:00
-- url     : https://prove2.me/theorems/f446b77b-3803-4107-bd63-cbf1fb00c0aa
-- statement:
--   **Nisan-Szegedy 1994, Lemma 2 — the integer-grid distinguishing polynomial bound.**
--
--   For every univariate real polynomial $Q \in \mathbb{R}[X]$ of degree $\le d$ that satisfies
--   $$Q(0) = 0, \qquad Q(1) = 1, \qquad |Q(t)| \le 1 \text{ for every } t \in \{0, 1, \ldots, b\}$$
--   (with $b \ge 1$), we have
--   $$b \;\le\; 2 \, d^2.$$
--
--   This is the *bundled* version of the classical Markov-brothers-on-the-integer-grid argument used in the polynomial-method proof of $\mathrm{bs}(f) \le 2 \deg(f)^2$.
--
--   **Why a bundled hypothesis is needed.** The naive form "any polynomial of degree $\le d$ bounded by $1$ on $\{0, 1, \ldots, b\}$ has $|Q'(c)| \le 2 d^2 / b$ on $[0, b]$" is *false* in general: the continuous extension constant from Ehlich-Zeller / Coppersmith-Rivlin can grow as $\exp(d^2 / b)$, so chaining "Ehlich-Zeller continuous extension" with "classical Markov on intervals" gives a worse constant than $2 d^2 / b$.
--
--   Nisan and Szegedy circumvent this by using the *additional* value constraints $Q(0) = 0$ and $Q(1) = 1$, together with the integer-grid bound, to derive the conclusion directly via a tightened Markov-on-the-grid argument that exploits the constrained structure (rather than passing through the continuous interval).
--
--   Likely proof strategy (NOT formalised here): combine a discrete-derivative bound with the constrained values to conclude $b \le 2 d^2$ without invoking Ehlich-Zeller. Estimated 600-1000 Lean lines, may need its own sub-decomposition (discrete derivatives, Markov inequality on integer points, the specific exploitation of $Q(0) = 0$, etc.).
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313, Lemma 2 (the integer-grid distinguishing polynomial bound used in their proof of bs(f) ≤ 2 deg(f)²).

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

/-!
# NS 1994 Lemma 2 — integer-grid distinguishing polynomial bound

Replaces the over-strong (and disprovable) `markov_brothers_integer_grid`.
Bundles the *specific* hypotheses Nisan–Szegedy use in the proof of
`bs(f) ≤ 2 deg(f)²`:

* `Q : Polynomial ℝ` of degree `≤ d`,
* `Q(0) = 0`,  `Q(1) = 1`,
* `|Q(t)| ≤ 1` on the integer grid `{0, 1, …, b}`,

and concludes `b ≤ 2 d²` *directly*. This is exactly NS Lemma 2; the proof
combines a tightened Markov-on-integer-grid argument with the value
constraints `Q(0)=0, Q(1)=1` to avoid the Ehlich–Zeller blow-up that breaks
the generic continuous-Markov composition.

Left as a platform leaf — DEFERRED. Estimated 600–1000 lines, may need
its own 4th-layer decomposition (e.g. discrete derivative bounds, the
Bernstein inequality variant on integer grids, etc.).

Why the previous `markov_brothers_integer_grid` is wrong: the bound
`|Q'(c)| ≤ 2 d² / b` is *false* in general for arbitrary polynomials
bounded by 1 on the integer grid; the continuous extension constant from
Ehlich–Zeller can grow as `exp(d²/b)`. NS sidestep this by using the
specific structure `Q(0) = 0, Q(1) = 1` directly, which is what this v2
statement encodes.
-/

/-- **Nisan–Szegedy 1994, Lemma 2.** A polynomial `Q : ℝ[X]` of degree
`≤ d` that vanishes at `0`, equals `1` at `1`, and is absolutely bounded
by `1` on the integer grid `{0, 1, …, b}` (with `b ≥ 1`) admits the bound
`b ≤ 2 d²`. -/

theorem markov_brothers_integer_grid_v2
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_zero : Q.eval 0 = 0) (h_one : Q.eval 1 = 1)
    (h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1) :
    b ≤ 2 * d^2 := by sorry
