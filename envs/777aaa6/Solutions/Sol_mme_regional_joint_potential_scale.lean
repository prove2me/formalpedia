-- Prove2me | solution 1 for mme_regional_joint_potential_scale
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T23:37:29.553722+00:00
-- url     : https://prove2.me/submissions/0210d1d2-725f-4d74-951c-bc1b606610f6

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Mathlib.Tactic.Ring
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic

open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

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


open MME.RegionRate

private theorem mass_entropy_scale {W : Type*} [Fintype W] (k : ℕ) (x : W → ℕ) :
    massEntropy (fun w => ((k * x w : ℕ) : ℝ)) =
      (k : ℝ) * massEntropy (fun w => (x w : ℝ)) := by
  simpa only [Nat.cast_mul] using
    (mme_regional_mass_entropy_algebra (C := Unit) (W := W)).1 (k : ℝ)
      (fun w => (x w : ℝ))

private theorem potential_scale {C W : Type*} [Fintype C] [Fintype W]
    (k : ℕ) (mu : C → W → ℕ) :
    potential (fun c w => k * mu c w) = (k : ℝ) * potential mu := by
  rw [(mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    (mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => mass_entropy_scale k (mu c))

private theorem part_count_scale {C W G : Type*} [Fintype C]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ)
    (k : ℕ) (s : {c : C // boundary c} ⊕ G) (w : W) :
    partCount boundary group (fun c w => k * mu c w) s w =
      k * partCount boundary group mu s w := by
  classical
  cases s with
  | inl c => rfl
  | inr g => simp [partCount, Finset.mul_sum, mul_ite]

/-- Replicating the regional split counts multiplies their joint entropy
by the replication factor, including profiles with zero counts. -/
theorem solution {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) :
    jointPotential (fun r c => k * m r c) = (k : ℝ) * jointPotential m := by
  simp only [jointPotential, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => mass_entropy_scale k (m r))

private theorem coarse_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) (i : Fin 3) :
    coarsePotential (fun r c => k * m r c) i = (k : ℝ) * coarsePotential m i := by
  simp only [coarsePotential, marginalCounts, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => mass_entropy_scale k _)

private theorem penalty_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (k : ℕ) (hk : 0 < k) :
    penaltyPotential (fun r => k * n r) (fun r c => k * m r c) =
      (k : ℝ) * penaltyPotential n m := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [penaltyPotential, Nat.cast_mul, mul_div_mul_left _ _ hk',
    mul_assoc, Finset.mul_sum]

private theorem parent_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    parentPotential htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c w => k * mu c w) = (k : ℝ) * parentPotential htotal n m mu := by
  have heq (r : Fin R) :
      parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
        (fun c w => k * mu c w) r = parentMixture htotal n m mu r := by
    funext w
    exact mme_parent_mixture_scale htotal n m mu k hk r w
  simp only [parentPotential, heq, Nat.cast_mul, mul_assoc, Finset.mul_sum]

private theorem compatibility_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} (i : Fin 2)
    (mu : Cell half R parent → W → ℕ) (k : ℕ) :
    compatibilityPotential i (fun c w => k * mu c w) =
      (k : ℝ) * compatibilityPotential i mu := by
  simp only [compatibilityPotential]
  have heq : partCount (yzBoundary i) (modeGroup (yzMode i)) (fun c w => k * mu c w) =
      fun s w => k * partCount (yzBoundary i) (modeGroup (yzMode i)) mu s w := by
    funext s w
    exact part_count_scale _ _ _ _ _ _
  rw [heq, potential_scale]

/-- Uniform replication scales the minimum of the three summed regional
rates exactly; normalized parent profiles and entropy penalties are unchanged. -/
private theorem mme_regional_rate_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    regionalRate htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) = (k : ℝ) * regionalRate htotal n m mu := by
  simp only [regionalRate, coarse_potential_scale, penalty_potential_scale n m k hk,
    parent_potential_scale htotal n m _ k hk, compatibility_potential_scale,
    ← mul_sub, mul_min_of_nonneg _ _ (Nat.cast_nonneg k)]

/-- The entropy exponent controlling the hash scale is linear under uniform
replication, with the tolerance fixed before choosing the replication factor. -/
private theorem mme_regional_scale_exponent_scale {half R ell : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) (k : ℕ) (hk : 0 < k) :
    scaleExponent htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) eps =
        (k : ℝ) * scaleExponent htotal n m mu eps := by
  rw [scaleExponent, scaleExponent, solution,
    mme_regional_rate_scale htotal n m mu k hk]
  simp only [← Finset.mul_sum, Nat.cast_mul]
  ring


#print axioms solution
