-- Prove2me | Definitions.Def_MachineLearning_BonferroniMarginals_Stability
-- name    : MachineLearning_BonferroniMarginals_Stability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:38:13.552964+00:00
-- url     : https://prove2.me/theorems/2b5cf576-0bd7-499b-8700-8ed49abd5893
-- title:
--   Aether Catalog definitions — MachineLearning_BonferroniMarginals_Stability
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.BonferroniMarginals.Stability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/BonferroniMarginals/Stability.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity

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

namespace BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}

/-- The Cauchy–Schwarz gap of a family, as an integer:
`|cover|·∑_{(i,j)}|Aᵢ∩Aⱼ| − (∑ᵢ|Aᵢ|)² ≥ 0`. -/
def csGap (I : Finset ι) (A : ι → Finset Ω) : ℤ :=
  ((cover I A).card : ℤ) * (∑ x ∈ cover I A, (mult I A x : ℤ) ^ 2)
    - (∑ x ∈ cover I A, (mult I A x : ℤ)) ^ 2







end BonferroniMarginals


