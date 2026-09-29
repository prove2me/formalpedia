-- Prove2me | solution 1 for QRResidual.perm_null_tail
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:22:36.101973+00:00
-- url     : https://prove2.me/submissions/82fb9c80-1c91-4aed-9008-6b0a286364f9

-- Sol generated from MachineLearning/QRResidual/PermutationNull.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_PermutationNull
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_perm_null_mean_lift
import Theorems.Thm_QRResidual_sqNorm_nonneg

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
    (hr : ∑ i, (y - g) i = 0) (hv : ∑ i, v i = 0) (hvn : sqNorm v ≠ 0) (htss : 0 < tss y)
    {t : ℝ} :
    ((Finset.univ.filter fun σ : Equiv.Perm ι =>
        t ≤ (dot (y - g) (fun i => v (σ i))) ^ 2 / (sqNorm v * tss y)).card : ℝ) * t
      * ((Fintype.card ι : ℝ) - 1)
      ≤ (Fintype.card (Equiv.Perm ι) : ℝ) * (1 - rsqOf y g) := by
  classical
  have hvpos : 0 < sqNorm v := lt_of_le_of_ne (sqNorm_nonneg v) (Ne.symm hvn)
  set f : Equiv.Perm ι → ℝ :=
    fun σ => (dot (y - g) (fun i => v (σ i))) ^ 2 / (sqNorm v * tss y) with hf
  have hfnn : ∀ σ : Equiv.Perm ι, 0 ≤ f σ := by
    intro σ; rw [hf]; positivity
  set S := Finset.univ.filter fun σ : Equiv.Perm ι => t ≤ f σ with hS
  have hlow : (S.card : ℝ) * t ≤ ∑ σ ∈ S, f σ := by
    have := Finset.card_nsmul_le_sum S f t (fun σ hσ => (Finset.mem_filter.1 hσ).2)
    simpa [nsmul_eq_mul] using this
  have hsub : (∑ σ ∈ S, f σ) ≤ ∑ σ : Equiv.Perm ι, f σ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun σ _ _ => hfnn σ)
  have hmean := perm_null_mean_lift (y := y) (g := g) (v := v) hn hr hv hvn htss
  have hcard : (0 : ℝ) < (Fintype.card (Equiv.Perm ι) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm ι) := Fintype.card_pos
    exact_mod_cast this
  have hn1 : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
    linarith
  have htot : (∑ σ : Equiv.Perm ι, f σ) * ((Fintype.card ι : ℝ) - 1)
      = (Fintype.card (Equiv.Perm ι) : ℝ) * (1 - rsqOf y g) := by
    field_simp at hmean
    linarith [hmean]
  have hchain : (S.card : ℝ) * t ≤ ∑ σ : Equiv.Perm ι, f σ := le_trans hlow hsub
  nlinarith [hchain, hn1, htot]
