-- Prove2me | solution 1 for QRResidual.perm_null_mean_lift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:20:48.965976+00:00
-- url     : https://prove2.me/submissions/a88191eb-92c6-489f-8d40-34c32651ccc1

-- Sol generated from MachineLearning/QRResidual/PermutationNull.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_PermutationNull
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_perm_null_sum_sq_dot
import Theorems.Thm_QRResidual_sqNorm_nonneg
import Theorems.Thm_QRResidual_sqNorm_residual_eq

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

open QRResidual

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Reindexing sums over the symmetric group -/



/-! ## The pair sum over the symmetric group -/






/-! ## The calibration identity -/




/-! ## A tail bound for the null, and the exp-585 instance -/




open QRResidual in
theorem solution{y g v : ι → ℝ} (hn : 2 ≤ Fintype.card ι)
    (hr : ∑ i, (y - g) i = 0) (hv : ∑ i, v i = 0) (hvn : sqNorm v ≠ 0) (htss : 0 < tss y) :
    (∑ σ : Equiv.Perm ι, (dot (y - g) (fun i => v (σ i))) ^ 2 / (sqNorm v * tss y))
        / (Fintype.card (Equiv.Perm ι) : ℝ)
      = (1 - rsqOf y g) / ((Fintype.card ι : ℝ) - 1) := by
  have hcard : (0 : ℝ) < (Fintype.card (Equiv.Perm ι) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm ι) := Fintype.card_pos
    exact_mod_cast this
  have hn1 : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
    linarith
  have hkey := perm_null_sum_sq_dot (r := y - g) (v := v) hn hr hv
  have hres : sqNorm (y - g) = (1 - rsqOf y g) * tss y := sqNorm_residual_eq htss
  have hpull : (∑ σ : Equiv.Perm ι, (dot (y - g) (fun i => v (σ i))) ^ 2 / (sqNorm v * tss y))
      = (∑ σ : Equiv.Perm ι, (dot (y - g) (fun i => v (σ i))) ^ 2) / (sqNorm v * tss y) := by
    rw [Finset.sum_div]
  rw [hpull]
  rw [div_div, div_eq_div_iff (by positivity) (ne_of_gt hn1)]
  have hvpos : 0 < sqNorm v := lt_of_le_of_ne (sqNorm_nonneg v) (Ne.symm hvn)
  rw [hres] at hkey
  field_simp at hkey ⊢
  linear_combination hkey
