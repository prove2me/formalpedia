-- Prove2me | Theorems.Thm_BonferroniMarginals_sq_spread_le_gap
-- name    : BonferroniMarginals.sq_spread_le_gap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:27:12.26667+00:00
-- url     : https://prove2.me/theorems/433fe92d-a50f-4698-aa57-7d1c51adb548
-- title:
--   Quantitative rigidity.
-- statement:
--   **Quantitative rigidity.**  Any two covered points have multiplicities
--   differing by at most the square root of the Cauchy–Schwarz gap.
--
--   ```lean
--   theorem BonferroniMarginals.sq_spread_le_gap(I : Finset ι) (A : ι → Finset Ω) {x y : Ω}
--       (hx : x ∈ cover I A) (hy : y ∈ cover I A) :
--       ((mult I A x : ℤ) - (mult I A y : ℤ)) ^ 2 ≤ csGap I A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BonferroniMarginals/Stability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BonferroniMarginals/Stability.lean#L62

-- Thm stub generated from MachineLearning/BonferroniMarginals/Stability.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_Stability

/-!
# Quantitative rigidity: near-tightness forces near-regularity

`Rigidity.lean` characterises *exact* equality in the second-moment bound
`(∑ᵢ|Aᵢ|)² ≤ |cover| · ∑_{(i,j)}|Aᵢ ∩ Aⱼ|`: it holds iff the coverage
multiplicity is constant.  Exact statements of that kind are fragile, so this
file upgrades the characterisation to a **stability** statement with an explicit
modulus.

Main results.

* `sq_spread_le_gap` — for any two covered points `x, y`,
  `(mult x − mult y)² ≤ |cover|·∑_{(i,j)}|Aᵢ∩Aⱼ| − (∑ᵢ|Aᵢ|)²`.
  The whole spread of the multiplicity function is controlled by the square root
  of the Cauchy–Schwarz gap.
* `regular_of_gap_zero` — the exact rigidity statement re-derived as the
  degenerate case, and `mult_eq_of_gap_lt_one` : a gap smaller than `1` already
  forces exact regularity (the gap is an integer).
* `bonferroni_defect_le_gap` — the Bonferroni defect `∑ₓ(mult x − 1)²` of
  `Rigidity.lean` is itself controlled: for a family whose Cauchy–Schwarz gap is
  `g` and whose average multiplicity is `1`, the defect is at most `g`.

Machine-learning reading: an ensemble whose second-order statistics are within
`g` of the Corrádi extremal profile has all coverage multiplicities within
`√g` of each other — the failure mass is *uniformly* spread, quantitatively.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

theorem BonferroniMarginals.sq_spread_le_gap(I : Finset ι) (A : ι → Finset Ω) {x y : Ω}
    (hx : x ∈ cover I A) (hy : y ∈ cover I A) :
    ((mult I A x : ℤ) - (mult I A y : ℤ)) ^ 2 ≤ csGap I A := by sorry
