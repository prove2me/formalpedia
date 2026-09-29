-- Prove2me | solution 1 for QRResidual.permPairSum_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:15:16.201556+00:00
-- url     : https://prove2.me/submissions/72dc8503-65cd-4f03-a56e-b8111022445c

-- Sol generated from MachineLearning/QRResidual/PermutationNull.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_PermutationNull
import Theorems.Thm_QRResidual_exists_perm_two_point

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

/-- Right translation is a bijection of the symmetric group, so it leaves sums invariant. -/
theorem sum_perm_mul_right (τ : Equiv.Perm ι) (f : Equiv.Perm ι → ℝ) :
    ∑ σ : Equiv.Perm ι, f (σ * τ) = ∑ σ : Equiv.Perm ι, f σ :=
  Fintype.sum_bijective (· * τ) (Group.mulRight_bijective τ) _ _ fun _ => rfl


/-! ## The pair sum over the symmetric group -/


/-- Off the diagonal, `W(i,j)` does not depend on the pair. -/
theorem permSum_pair_const_offdiag (v : ι → ℝ) {i j i' j' : ι} (hij : i ≠ j) (hij' : i' ≠ j') :
    permPairSum v i j = permPairSum v i' j' := by
  obtain ⟨τ, hτ1, hτ2⟩ := exists_perm_two_point hij hij'
  calc permPairSum v i j
      = ∑ σ : Equiv.Perm ι, v ((σ * τ) i') * v ((σ * τ) j') := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp [Equiv.Perm.mul_apply, hτ1, hτ2]
    _ = permPairSum v i' j' :=
        sum_perm_mul_right τ (fun σ => v (σ i') * v (σ j'))

/-- On the diagonal, `W(i,i)` does not depend on the point. -/
theorem permSum_pair_const_diag (v : ι → ℝ) (i i' : ι) :
    permPairSum v i i = permPairSum v i' i' := by
  set τ := Equiv.swap i' i with hτ
  have hτ1 : τ i' = i := by simp [hτ]
  calc permPairSum v i i
      = ∑ σ : Equiv.Perm ι, v ((σ * τ) i') * v ((σ * τ) i') := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp [Equiv.Perm.mul_apply, hτ1]
    _ = permPairSum v i' i' := sum_perm_mul_right τ (fun σ => v (σ i') * v (σ i'))



/-! ## The calibration identity -/




/-! ## A tail bound for the null, and the exp-585 instance -/




open QRResidual in
theorem solution{v : ι → ℝ} (hn : 2 ≤ Fintype.card ι) (i₀ j₀ : ι) (hij₀ : i₀ ≠ j₀) :
    (Fintype.card ι : ℝ) * permPairSum v i₀ i₀
        + (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * permPairSum v i₀ j₀
      = ∑ i, ∑ j, permPairSum v i j := by
  have hrow : ∀ i : ι, (∑ j, permPairSum v i j)
      = permPairSum v i₀ i₀ + ((Fintype.card ι : ℝ) - 1) * permPairSum v i₀ j₀ := by
    intro i
    have hsplit : (∑ j, permPairSum v i j)
        = permPairSum v i i + ∑ j ∈ Finset.univ.erase i, permPairSum v i j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hoff : ∀ j ∈ Finset.univ.erase i, permPairSum v i j = permPairSum v i₀ j₀ := by
      intro j hj
      exact permSum_pair_const_offdiag v (Ne.symm (Finset.ne_of_mem_erase hj)) hij₀
    rw [hsplit, Finset.sum_congr rfl hoff, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      permSum_pair_const_diag v i i₀]
    have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      have : 1 ≤ Fintype.card ι := le_trans (by norm_num) hn
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  ring
