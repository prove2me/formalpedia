-- Prove2me | Definitions.Def_MachineLearning_QRResidual_PermutationNull
-- name    : MachineLearning_QRResidual_PermutationNull
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:56:35.551883+00:00
-- url     : https://prove2.me/theorems/a197ac13-fb49-452d-8af3-366821206122
-- title:
--   Aether Catalog definitions — MachineLearning_QRResidual_PermutationNull
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.QRResidual.PermutationNull`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/QRResidual/PermutationNull.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling

/-!
# Exact calibration of the permutation null for an `R²` increment

The verdict of experiment 585 rests on two numbers: an observed increment
`ΔR² = 0.01946`, and a permutation null obtained from 500 joint row-shuffles of the
covariate block, with `p = 0.389` and `q95 = 0.046`.  The permutation null is normally
treated as a Monte-Carlo object.  It is not: for a *single* centred covariate its exact
first moment is a closed-form function of the sample size alone.

Main results.

* `exists_perm_two_point` — sharp 2-transitivity of the symmetric group, in the explicit
  two-swap form needed below.
* `permSum_pair_const_offdiag`, `permSum_pair_const_diag` — the sum
  `W(i,j) = Σ_{σ} v(σ i) v(σ j)` over the whole symmetric group depends only on whether
  `i = j`.
* `perm_null_sum_sq_dot` — **the calibration identity**: for a centred residual `r` and a
  centred covariate `v` on a sample of size `n`,
  `Σ_{σ ∈ S_n} ⟨r, v∘σ⟩² = n! · ‖r‖²‖v‖² / (n−1)`,
  i.e. the *mean squared* residual correlation under a random row shuffle is exactly
  `1/(n−1)` of the maximum.
* `perm_null_mean_lift` — hence the mean permutation-null `R²` increment of one covariate
  is exactly `(1 − R²₀)/(n − 1)`: the null is calibrated by the baseline fit and the sample
  size, with no distributional assumption whatsoever.
* `perm_null_tail`, `exp585_perm_null_tail` — a Markov tail bound on the null, and its
  numeric instance: at the reported baseline `R²₀ = 0.4112` and any sample of at least
  `237` moduli, at most a `0.05` fraction of shuffles reach an increment of `0.05`.  This
  is consistent with, and independently bounds, the reported `q95 = 0.046`.

Together with `BlockCeiling`, this turns the experiment's null verdict into two theorems:
a *ceiling* on what the covariate block could ever have achieved, and a *calibration* of
the reference distribution against which the observed increment was judged.
-/

namespace QRResidual

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Reindexing sums over the symmetric group -/



/-! ## The pair sum over the symmetric group -/

/-- The total pair statistic `W(i,j) = Σ_σ v(σ i)·v(σ j)` of a covariate. -/
def permPairSum (v : ι → ℝ) (i j : ι) : ℝ := ∑ σ : Equiv.Perm ι, v (σ i) * v (σ j)





/-! ## The calibration identity -/




/-! ## A tail bound for the null, and the exp-585 instance -/



end QRResidual


