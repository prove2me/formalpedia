-- Prove2me | solution 1 for QRResidual.perm_null_sum_sq_dot
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:18:05.930232+00:00
-- url     : https://prove2.me/submissions/e573e912-091c-4413-b74a-6fcef366ce2b

-- Sol generated from MachineLearning/QRResidual/PermutationNull.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_PermutationNull
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_exists_perm_two_point
import Theorems.Thm_QRResidual_permPairSum_split

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

/-- Summing the diagonal statistic over the sample gives `|S_n| · ‖v‖²`. -/
theorem sum_permPairSum_diag (v : ι → ℝ) :
    ∑ i, permPairSum v i i = (Fintype.card (Equiv.Perm ι) : ℝ) * sqNorm v := by
  unfold permPairSum
  rw [Finset.sum_comm]
  have h : ∀ σ : Equiv.Perm ι, (∑ i, v (σ i) * v (σ i)) = sqNorm v := by
    intro σ
    have : (∑ i, v (σ i) * v (σ i)) = ∑ i, (v (σ i)) ^ 2 := by
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, sqNorm]
    exact Equiv.sum_comp σ (fun i => (v i) ^ 2)
  simp [h, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- For a **centred** covariate the full pair statistic sums to zero. -/
theorem sum_permPairSum_all {v : ι → ℝ} (hv : ∑ i, v i = 0) :
    ∑ i, ∑ j, permPairSum v i j = 0 := by
  have hswap : ∀ i : ι, (∑ j, permPairSum v i j)
      = ∑ σ : Equiv.Perm ι, ∑ j, v (σ i) * v (σ j) := by
    intro i; unfold permPairSum; exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => hswap i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hzero : (∑ j, v (σ j)) = 0 := by rw [Equiv.sum_comp σ v]; exact hv
  calc (∑ i, ∑ j, v (σ i) * v (σ j))
      = (∑ i, v (σ i)) * (∑ j, v (σ j)) := by
        rw [Finset.sum_mul_sum]
    _ = 0 := by rw [hzero, mul_zero]

/-! ## The calibration identity -/




/-! ## A tail bound for the null, and the exp-585 instance -/




open QRResidual in
theorem solution{r v : ι → ℝ} (hn : 2 ≤ Fintype.card ι)
    (hr : ∑ i, r i = 0) (hv : ∑ i, v i = 0) :
    ((Fintype.card ι : ℝ) - 1) * (∑ σ : Equiv.Perm ι, (dot r (fun i => v (σ i))) ^ 2)
      = (Fintype.card (Equiv.Perm ι) : ℝ) * (sqNorm r * sqNorm v) := by
  classical
  -- two distinct sample points exist
  obtain ⟨i₀, j₀, hij₀⟩ : ∃ i₀ j₀ : ι, i₀ ≠ j₀ := by
    have h1 : 1 < Fintype.card ι := hn
    exact Fintype.exists_pair_of_one_lt_card h1
  set n : ℝ := (Fintype.card ι : ℝ) with hn'
  set D : ℝ := permPairSum v i₀ i₀ with hD
  set T : ℝ := permPairSum v i₀ j₀ with hT
  -- expand the square of the shuffled inner product
  have hexpand : (∑ σ : Equiv.Perm ι, (dot r (fun i => v (σ i))) ^ 2)
      = ∑ i, ∑ j, r i * r j * permPairSum v i j := by
    have hstep : ∀ σ : Equiv.Perm ι, (dot r (fun i => v (σ i))) ^ 2
        = ∑ i, ∑ j, (r i * v (σ i)) * (r j * v (σ j)) := by
      intro σ
      rw [dot, sq, Finset.sum_mul_sum]
    calc (∑ σ : Equiv.Perm ι, (dot r (fun i => v (σ i))) ^ 2)
        = ∑ σ : Equiv.Perm ι, ∑ i, ∑ j, (r i * v (σ i)) * (r j * v (σ j)) := by
          exact Finset.sum_congr rfl fun σ _ => hstep σ
      _ = ∑ i, ∑ j, ∑ σ : Equiv.Perm ι, (r i * v (σ i)) * (r j * v (σ j)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, r i * r j * permPairSum v i j := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          unfold permPairSum
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
  -- the pair statistic takes only two values
  have hvalue : ∀ i j : ι, permPairSum v i j = if i = j then D else T := by
    intro i j
    by_cases h : i = j
    · subst h; simp [hD, permSum_pair_const_diag v i i₀]
    · simp [h, hT, permSum_pair_const_offdiag v h hij₀]
  have hrow : ∀ i : ι, (∑ j, r i * r j * permPairSum v i j)
      = r i * (r i * D) + r i * ((∑ j, r j) - r i) * T := by
    intro i
    have hsplit : (∑ j, r i * r j * permPairSum v i j)
        = r i * r i * permPairSum v i i
          + ∑ j ∈ Finset.univ.erase i, r i * r j * permPairSum v i j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hoff : ∀ j ∈ Finset.univ.erase i, r i * r j * permPairSum v i j = r i * r j * T := by
      intro j hj
      rw [hvalue i j, if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
    have herase : (∑ j ∈ Finset.univ.erase i, r j) = (∑ j, r j) - r i := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact Finset.add_sum_erase _ _ (Finset.mem_univ i)
    rw [hsplit, Finset.sum_congr rfl hoff, hvalue i i, if_pos rfl, ← Finset.sum_mul,
      ← Finset.mul_sum, herase]
    ring
  have htotal : (∑ i, ∑ j, r i * r j * permPairSum v i j) = sqNorm r * D - sqNorm r * T := by
    rw [Finset.sum_congr rfl fun i _ => hrow i, hr]
    have : ∀ i : ι, r i * (r i * D) + r i * (0 - r i) * T = (r i) ^ 2 * D - (r i) ^ 2 * T := by
      intro i; ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul]
    rfl
  -- the centred covariate forces `n·D + n(n−1)·T = 0`
  have hzero : n * D + n * (n - 1) * T = 0 := by
    rw [permPairSum_split (v := v) hn i₀ j₀ hij₀, sum_permPairSum_all hv]
  have hdiag : n * D = (Fintype.card (Equiv.Perm ι) : ℝ) * sqNorm v := by
    have := sum_permPairSum_diag v
    rw [Finset.sum_congr rfl fun i _ => permSum_pair_const_diag v i i₀, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ] at this
    exact this
  have h2n : (2 : ℝ) ≤ n := by rw [hn']; exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n - 1 := by linarith
  have hTval : (n - 1) * T = -D := by
    have hnpos : (0 : ℝ) < n := by linarith
    have : n * ((n - 1) * T + D) = 0 := by linarith [hzero]
    have h2 := mul_eq_zero.1 this
    rcases h2 with h | h
    · exact absurd h hnpos.ne'
    · linarith
  rw [hexpand, htotal]
  have hfinal : (n - 1) * (sqNorm r * D - sqNorm r * T)
      = sqNorm r * ((n - 1) * D - (n - 1) * T) := by ring
  rw [hfinal, hTval]
  have : (n - 1) * D - -D = n * D := by ring
  rw [this, hdiag]
  ring
