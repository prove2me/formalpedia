-- Prove2me | solution 1 for mme_released_interior_scaled_partition_parent_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:08:57.035539+00:00
-- url     : https://prove2.me/submissions/c02abc31-8c59-45cd-ba01-944ae45a5196

import Theorems.Thm_mme_released_interior_weighted_parent_center
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
import Theorems.Thm_mme_regional_parent_windows_imply_global_histogram_window_allow_empty

open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization

private theorem mme_released_interior_regional_total
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = []) :
    (∑ r : Fin 6, regionalSize owner s r) = denominator ^ 4 := by
  obtain ⟨reference, href, htotal, hrest⟩ :=
    mme_released_interior_scaled_integer_profile_constraints_exact owner s hi 1 (by decide)
  simpa only [one_mul] using htotal

/-- Replicating every occurrence preserves each normalized child profile. -/
private theorem mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
private theorem mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'



/-- At every positive integer scale, the six regional windows imply a
full-word histogram window centered at the same released distribution. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (k : ℕ) (hk : 0 < k) :
    ∃ positions : (Σ r : Fin 6, Fin (k * (regionalSize owner s) r)) ≃
        Fin (k * denominator ^ 4),
      ∀ (i : Fin 3) (f : Fin (k * denominator ^ 4) → CompleteWord 3) (eps : ℝ),
        parentTypical (parent_total s) (fun r => k * (regionalSize owner s) r)
          (fun r c => k * (splitCount owner s) r c) (fun c w => k * (integerProfile owner s) i c w) eps
          (fun p =>
            let v := (completeWordSplitEquiv 2 (by decide)) (f (positions ⟨p.1,p.2.1⟩))
            ![v.1,v.2] p.2.2) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) // f p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows owner s).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  have hT : (∑ r : Fin 6, k * (regionalSize owner s) r) = k * denominator ^ 4 := by
    rw [← Finset.mul_sum, mme_released_interior_regional_total owner s hi]
  have hcard : Fintype.card (Σ r : Fin 6, Fin (k * (regionalSize owner s) r)) =
      Fintype.card (Fin (k * denominator ^ 4)) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hT
  let positions := Fintype.equivOfCardEq hcard
  refine ⟨positions, ?_⟩
  intro i f eps htypical w
  let pair := (completeWordSplitEquiv 2 (by decide)).trans
    (finTwoArrowEquiv (CompleteWord 2)).symm
  have h := mme_regional_parent_windows_imply_global_histogram_window_allow_empty
    (parent_total s) (fun r c => k * (splitCount owner s) r c) (fun c w => k * (integerProfile owner s) i c w)
    positions f pair eps
    hT (Nat.mul_pos hk (by norm_num [denominator])) htypical w
  have hpair (v : CompleteWord 3) : pair v =
      ![((completeWordSplitEquiv 2 (by decide)) v).1,
        ((completeWordSplitEquiv 2 (by decide)) v).2] := rfl
  have hweight (r : Fin 6) :
      ((k * (regionalSize owner s) r : ℕ) : ℝ) / (k * denominator ^ 4 : ℕ) =
        ((regionalSize owner s) r : ℝ) / (denominator : ℝ) ^ 4 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact mul_div_mul_left _ _ hk'
  simp only [mme_parent_mixture_scale _ _ _ _ k hk, hweight, hpair] at h
  rw [mme_released_interior_weighted_parent_center owner s hi i w] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h




#print axioms solution
