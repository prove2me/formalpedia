-- Prove2me | Theorems.Thm_Shared_UnimodalArgmaxBracketing_binomialWeight_nat_bracket_gap
-- name    : Shared.UnimodalArgmaxBracketing.binomialWeight_nat_bracket_gap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:51:30.60382+00:00
-- url     : https://prove2.me/theorems/76ded9a4-3252-43c1-86d3-2f57a2586a9d
-- title:
--   For natural weights `p, q â¥ 1` the plateau (gap `1`) occurs exactly when
-- statement:
--   For natural weights `p, q â¥ 1` the plateau (gap `1`) occurs exactly when
--   `(p + q) â£ (n + 1) * p`.
--
--   ```lean
--   theorem Shared.UnimodalArgmaxBracketing.binomialWeight_nat_bracket_gap{P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) :
--       lastArgmax n (binomialWeight n (P : ℝ) (Q : ℝ))
--           = firstArgmax n (binomialWeight n (P : ℝ) (Q : ℝ)) + 1 ↔
--         (P + Q) ∣ (n + 1) * P := by sorry
--
--
--
--
--
--
--   /-! ## The largest term of the binomial expansion -/
--
--
--   /-! ## Every degree is a Newton-polygon vertex
--
--   Strict log-concavity says that the points `(k, log C(n,k))` are in *strictly convex
--   position*.  Equivalently: after tilting by a suitable weight `p^k` every single
--   degree `d ≤ n` becomes the **unique** maximiser.  This is the sweep of the argmax as
--   the threshold `θ` runs through `(0, n+1)`. -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/UnimodalArgmaxBinomial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/UnimodalArgmaxBinomial.lean#L306

-- Thm stub generated from Shared/UnimodalArgmaxBinomial.lean
import Mathlib
import Definitions.Def_Shared_UnimodalArgmaxBinomial
import Definitions.Def_Shared_UnimodalArgmaxBracketing
/-
# The two bracketing degrees of the binomial weights, explicitly

Companion to `Shared.UnimodalArgmaxBracketing`.  There the abstract theory was set
up: a strictly log-concave positive window `a 0, …, a n` is strictly unimodal and
its maximiser set is the interval `[firstArgmax, lastArgmax]` between the two
bracketing degrees, whose gap is `0` or `1`.

Here the abstract machine is run on the **binomial weights**

`binomialWeight n p q k = C(n,k) * p ^ k * q ^ (n - k)`  (`p, q > 0`),

the individual terms of the binomial theorem for `(p + q) ^ n`.  The output is a
completely explicit description of both bracketing degrees in terms of the single
real *mode parameter*

`modeParameter n p q = (n + 1) * p / (p + q)`.

Main results:

* `Nat.choose_mul_choose_lt_choose_sq` — strict log-concavity of a row of Pascal's
  triangle (`C(n,k) * C(n,k+2) < C(n,k+1)^2`), proved from
  `Nat.choose_succ_right_eq` alone.
* `binomialWeight_strictLogConcaveOn` — the weights form a strictly log-concave
  window.
* `binomialWeight_firstArgmax` : `d⁻ = ⌈θ⌉₊ - 1`,
  `binomialWeight_lastArgmax` : `d⁺ = ⌊θ⌋₊`.
* `binomialWeight_bracket_gap` : `d⁺ = d⁻ + 1 ↔ θ ∈ ℕ` — **the explicit comparison
  of the two bracketing degrees**.
* `binomialWeight_nat_bracket_gap` : for natural weights, the plateau occurs iff
  `(p + q) ∣ (n + 1) * p`.
* `choose_firstArgmax`, `choose_lastArgmax`, `choose_bracket_gap` : for `p = q = 1`
  the degrees are `n / 2` and `(n + 1) / 2`, and the plateau occurs iff `n` is odd.
* `binomialWeight_max_term_bracket` : the largest term of the binomial expansion is
  squeezed between `(p+q)^n / (n+1)` and `(p+q)^n`.
-/

open Shared
open UnimodalArgmaxBracketing

/-! ## Strict log-concavity of a row of Pascal's triangle -/


/-! ## The binomial weights -/



variable {n : ℕ} {p q : ℝ}





/-! ## The rise criterion -/




/-! ## The two bracketing degrees, explicitly -/




/-! ## The explicit comparison of the two bracketing degrees -/



/-! ## Dependence of the brackets on the parameters -/







/-! ## Arithmetic form of the comparison, and the classical case `p = q = 1` -/

theorem Shared.UnimodalArgmaxBracketing.binomialWeight_nat_bracket_gap{P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) :
    lastArgmax n (binomialWeight n (P : ℝ) (Q : ℝ))
        = firstArgmax n (binomialWeight n (P : ℝ) (Q : ℝ)) + 1 ↔
      (P + Q) ∣ (n + 1) * P := by sorry
