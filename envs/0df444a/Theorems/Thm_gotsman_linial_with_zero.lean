-- Prove2me | Theorems.Thm_gotsman_linial_with_zero
-- name    : gotsman_linial_with_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-06T20:38:31.677595+00:00
-- url     : https://prove2.me/theorems/eeb3be45-8024-421b-b5bb-59f6955e790c
-- statement:
--   **Gotsman–Linial 1992** (corrected applied form, with the $h(0) \le 0$ boundary case).
--
--   Let $h : \mathbb{N} \to \mathbb{R}$ be monotone with $h(0) \le 0$. Suppose that for every $m \ge 1$ and every set $S \subseteq Q_m$ of vertices of the $m$-cube with $|S| > 2^{m-1}$, there exists $v \in S$ whose internal degree (number of neighbours of $v$ inside $S$) satisfies
--   $$\deg_S(v) \ge h(m).$$
--   Then for every Boolean function $f : \{0,1\}^n \to \{0,1\}$,
--   $$h(\deg(f)) \le s(f),$$
--   where $\deg(f)$ is the polynomial degree of $f$ and $s(f)$ is its sensitivity.
--
--   This is the corrected form of `gotsman_linial`: the extra hypothesis $h(0) \le 0$ rescues the constant-function case ($\deg f = 0$ and $s(f) = 0$), where the original statement was unprovable because $\mathrm{hQ}$ only constrains $h$ at $m \ge 1$. Downstream consumers using $h(m) = \sqrt{m}$ supply $h(0) = 0 \le 0$ trivially.
-- source:
--   Gotsman, Chaim, and Nathan Linial. "The equivalence of two problems on the cube." Journal of Combinatorial Theory, Series A 61.1 (1992): 142-146. (Direction used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Definitions.Def_Hypercube
import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree
import Mathlib.Data.Real.Basic

/-!
# Gotsman–Linial 1992 (corrected applied form, including `polyDegree = 0`)

The classical equivalence used by Huang 2019 to lift an induced-subgraph
max-degree bound on the hypercube to a sensitivity–degree lower bound on
Boolean functions. We state only the direction actually needed by
Huang's Thm 1.4: *hypercube bound ⇒ sensitivity/degree bound*.

This is the corrected form that supersedes `gotsman_linial`. The original
statement was unprovable for `polyDegree f = 0` (constant Boolean
functions), because `hQ` only constrains `h` on `m > 0`, leaving `h 0`
unconstrained. Concrete counter-example to the un-corrected form:
`h(0) = 1/4`, `h(m) = √m` for `m ≥ 1` is monotone and satisfies `hQ`
(matching Huang's bound), but for `f ≡ false` the conclusion `1/4 ≤ 0`
is false.

The fix is the additional hypothesis `(h0 : h 0 ≤ 0)`. Downstream
consumers (e.g. `sensitivity_sq_ge_polyDegree`) supply this trivially
since they take `h = Real.sqrt`, where `h 0 = 0 ≤ 0`.
-/

/-- **Gotsman–Linial 1992** (direction used in Huang 2019 §1, with
    correct boundary case for constant functions).
    Let `h : ℕ → ℝ` be monotone with `h 0 ≤ 0`. If every induced
    subgraph of `Qₘ` of size `> 2^(m-1)` contains a vertex of internal
    degree at least `h m`, then for every Boolean function
    `f : {0,1}ⁿ → {0,1}`, the sensitivity `s(f)` is at least `h (deg f)`.
    -/

theorem gotsman_linial_with_zero
    (h : ℕ → ℝ) (hmono : Monotone h) (h0 : h 0 ≤ 0)
    (hQ : ∀ m, 0 < m → ∀ S : Finset (Fin m → Bool), 2 ^ (m - 1) < S.card →
        ∃ v ∈ S, h m ≤ (Hypercube.degreeIn m S v : ℝ))
    {n : ℕ} (f : BoolFunc n) :
    h (polyDegree f) ≤ (sensitivity f : ℝ) := by sorry
