-- Prove2me | solution 1 for mme_regional_rate_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T14:36:30.015327+00:00
-- url     : https://prove2.me/submissions/e1345bb7-e802-4c92-84be-67d4c531d147

import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_region_count_entropy_data
import Definitions.Def_mme_recursive_yz_compatibility
import Mathlib

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open scoped Classical

universe u

set_option autoImplicit false

/-!
# The regional rate is homogeneous of degree one

Scaling every multiplicity of a regional recipe by a common positive factor `t` scales its rate by
`t`. All three branches of `regionalRate` are sums of unnormalized entropies of the counts, and the
normalized distributions that appear inside them are unchanged by the scaling.
-/

private theorem negMulLog_smul (t y : ℝ) (ht : 0 < t) (hy : 0 ≤ y) :
    Real.negMulLog (t * y) = t * Real.negMulLog y - t * y * Real.log t := by
  rcases eq_or_lt_of_le hy with h | h
  · simp [Real.negMulLog, ← h]
  · rw [Real.negMulLog, Real.negMulLog, Real.log_mul (ne_of_gt ht) (ne_of_gt h)]
    ring

private theorem massEntropy_smul {W : Type*} [Fintype W] (t : ℝ) (ht : 0 < t)
    (x : W → ℝ) (hx : ∀ w, 0 ≤ x w) :
    massEntropy (fun w ↦ t * x w) = t * massEntropy x := by
  have hsum : (0 : ℝ) ≤ ∑ w, x w := Finset.sum_nonneg fun w _ ↦ hx w
  have hpoint : ∀ w, Real.negMulLog (t * x w)
      = t * Real.negMulLog (x w) - t * x w * Real.log t :=
    fun w ↦ negMulLog_smul t (x w) ht (hx w)
  have hentropy : entropy (fun w ↦ t * x w)
      = t * entropy x - t * (∑ w, x w) * Real.log t := by
    calc entropy (fun w ↦ t * x w)
        = ∑ w, (t * Real.negMulLog (x w) - t * x w * Real.log t) :=
          Finset.sum_congr rfl fun w _ ↦ hpoint w
      _ = (∑ w, t * Real.negMulLog (x w)) - ∑ w, t * x w * Real.log t :=
          Finset.sum_sub_distrib _ _
      _ = t * entropy x - t * (∑ w, x w) * Real.log t := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
          rfl
  have htotal : (∑ w, t * x w) = t * ∑ w, x w := by
    rw [Finset.mul_sum]
  simp only [massEntropy, hentropy, htotal]
  rw [negMulLog_smul t (∑ w, x w) ht hsum]
  ring

private theorem cellFrequency_smul {C : Type*} {W : Type*} [Fintype W]
    (mu : C → W → ℕ) (t : ℕ) (ht : 0 < t) (c : C) (w : W) :
    cellFrequency (fun c w ↦ t * mu c w) c w = cellFrequency mu c w := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  simp only [cellFrequency]
  rw [show ((∑ v, t * mu c v : ℕ) : ℝ) = (t : ℝ) * ((∑ v, mu c v : ℕ) : ℝ) by
    push_cast
    rw [Finset.mul_sum]]
  push_cast
  rw [mul_div_mul_left _ _ htR]

private theorem potential_smul {C : Type*} {W : Type*} [Fintype C] [Fintype W]
    (mu : C → W → ℕ) (t : ℕ) (ht : 0 < t) :
    potential (fun c w ↦ t * mu c w) = (t : ℝ) * potential mu := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  simp only [potential, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hsum : ((∑ w, t * mu c w : ℕ) : ℝ) = (t : ℝ) * ((∑ z, mu c z : ℕ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
  have hratio : (fun w ↦ (((t * mu c w : ℕ)) : ℝ) / ((t : ℝ) * ((∑ z, mu c z : ℕ) : ℝ)))
      = fun w ↦ ((mu c w : ℕ) : ℝ) / ((∑ z, mu c z : ℕ) : ℝ) := by
    funext w
    push_cast
    rw [mul_div_mul_left _ _ htR]
  rw [hsum, hratio]
  ring

theorem solution {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (t : ℕ) (ht : 0 < t) :
    regionalRate htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c)
        (fun i c w ↦ t * mu i c w)
      = (t : ℝ) * regionalRate htotal n m mu := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htR' : (t : ℝ) ≠ 0 := ne_of_gt htR
  -- the coarse branch
  have hmarginal : ∀ (i : Fin 3) (r : Fin R) (j : Fin (half + 1)),
      marginalCounts (fun r c ↦ t * m r c) i r j = t * marginalCounts m i r j := by
    intro i r j
    simp only [marginalCounts, Finset.mul_sum]
  have hcoarse : ∀ i, coarsePotential (fun r c ↦ t * m r c) i
      = (t : ℝ) * coarsePotential m i := by
    intro i
    simp only [coarsePotential, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have : (fun j ↦ ((marginalCounts (fun r c ↦ t * m r c) i r j : ℕ) : ℝ))
        = fun j ↦ (t : ℝ) * ((marginalCounts m i r j : ℕ) : ℝ) := by
      funext j
      rw [hmarginal i r j]
      push_cast
      ring
    rw [this, massEntropy_smul (t : ℝ) htR _ (fun j ↦ by positivity)]
  -- the penalty is scale invariant in its argument
  have hpenalty : penaltyPotential (fun r ↦ t * n r) (fun r c ↦ t * m r c)
      = (t : ℝ) * penaltyPotential n m := by
    simp only [penaltyPotential, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have harg : (fun c ↦ (((t * m r c : ℕ)) : ℝ) / ((t * n r : ℕ) : ℝ))
        = fun c ↦ ((m r c : ℕ) : ℝ) / ((n r : ℕ) : ℝ) := by
      funext c
      push_cast
      rw [mul_div_mul_left _ _ htR']
    rw [harg]
    push_cast
    ring
  -- the parent mixture is unchanged, so the parent branch scales
  have hmixture : ∀ (i : Fin 3) (r : Fin R),
      parentMixture htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c)
          (fun c w ↦ t * mu i c w) r
        = parentMixture htotal n m (mu i) r := by
    intro i r
    funext w
    simp only [parentMixture]
    have hfreq : ∀ (c : Cell half R parent) (v : W),
        cellFrequency (fun c w ↦ t * mu i c w) c v = cellFrequency (mu i) c v :=
      fun c v ↦ cellFrequency_smul (mu i) t ht c v
    simp only [hfreq]
    rw [show (∑ c, (((t * m r c : ℕ)) : ℝ) * cellFrequency (mu i) ⟨r, c⟩ (w 0) *
          cellFrequency (mu i) ⟨r, complement (htotal r) c⟩ (w 1))
        = (t : ℝ) * ∑ c, ((m r c : ℕ) : ℝ) * cellFrequency (mu i) ⟨r, c⟩ (w 0) *
          cellFrequency (mu i) ⟨r, complement (htotal r) c⟩ (w 1) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      push_cast
      ring]
    push_cast
    rw [mul_div_mul_left _ _ htR']
  have hparent : ∀ i, parentPotential htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c)
      (fun c w ↦ t * mu i c w) = (t : ℝ) * parentPotential htotal n m (mu i) := by
    intro i
    simp only [parentPotential, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [hmixture i r]
    push_cast
    ring
  have hcompat : ∀ (i : Fin 2) (j : Fin 3),
      compatibilityPotential i (fun c w ↦ t * mu j c w)
        = (t : ℝ) * compatibilityPotential i (mu j) := by
    intro i j
    simp only [compatibilityPotential]
    have hpart : partCount (yzBoundary i) (modeGroup (yzMode i)) (fun c w ↦ t * mu j c w)
        = fun s w ↦ t * partCount (yzBoundary i) (modeGroup (yzMode i)) (mu j) s w := by
      funext s w
      cases s with
      | inl c => simp [partCount]
      | inr g =>
        simp only [partCount, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        by_cases h : ¬ yzBoundary i c ∧ modeGroup (yzMode i) c = g
        · simp [h]
        · simp [h]
    rw [hpart, potential_smul _ t ht]
  simp only [regionalRate, hcoarse, hpenalty, hparent, hcompat]
  rw [← mul_sub, ← mul_sub, ← mul_sub, ← mul_min_of_nonneg _ _ (le_of_lt htR),
    ← mul_min_of_nonneg _ _ (le_of_lt htR)]
