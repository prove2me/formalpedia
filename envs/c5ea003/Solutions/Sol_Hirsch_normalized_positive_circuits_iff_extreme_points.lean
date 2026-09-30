-- Prove2me | solution 1 for Hirsch.normalized_positive_circuits_iff_extreme_points
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T21:35:23.89091+00:00
-- url     : https://prove2.me/submissions/9367eda0-1710-493c-b2f7-19458fba31ed

import Mathlib

open scoped BigOperators

/-! Finite positive-circuit completeness for linear tests on a nonnegative kernel.
No feasibility, Farkas, circuit-generation, or diameter theorem is assumed.
-/

namespace Hirsch.PositiveCircuitTests

noncomputable def supp {n : ℕ} (x : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

@[simp] theorem mem_supp {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    i ∈ supp x ↔ x i ≠ 0 := by
  classical
  simp [supp]

def NonnegNull {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ A x = 0

def Circuit {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ) : Prop :=
  NonnegNull A x ∧ x ≠ 0 ∧
    ∀ y, NonnegNull A y → y ≠ 0 → supp y ⊆ supp x → supp x ⊆ supp y

private theorem positive_coordinate {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) : ∃ i, 0 < x i := by
  by_contra h
  push_neg at h
  apply hne
  funext i
  exact le_antisymm (h i) (hx i)

/-- Subtract as far as possible in a supported direction with a positive entry. -/
private theorem prune {n : ℕ} (x y : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsub : supp y ⊆ supp x)
    (hy : ∃ i, 0 < y i) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ (x - t • y) i) ∧
      supp (x - t • y) ⊂ supp x := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => 0 < y i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hy
    exact ⟨i, by simp [s, hi]⟩
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image s (fun j => x j / y j) hs
  have hyi : 0 < y i := (Finset.mem_filter.mp hi).2
  have hxi : 0 < x i := by
    have hne : x i ≠ 0 := (mem_supp x i).mp
      (hsub ((mem_supp y i).mpr (ne_of_gt hyi)))
    exact lt_of_le_of_ne (hx i) (Ne.symm hne)
  let t : ℝ := x i / y i
  have ht : 0 < t := div_pos hxi hyi
  have hti : t * y i = x i := by
    exact div_mul_cancel₀ _ (ne_of_gt hyi)
  have hz : ∀ j, 0 ≤ (x - t • y) j := by
    intro j
    change 0 ≤ x j - t * y j
    by_cases hj : 0 < y j
    · have hratio : t ≤ x j / y j := hmin j (by simp [s, hj])
      have hprod : t * y j ≤ x j := (le_div_iff₀ hj).mp hratio
      linarith
    · have hprod : t * y j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (le_of_not_gt hj)
      linarith [hx j]
  have hzero : ∀ j, x j = 0 → y j = 0 := by
    intro j hj
    by_contra hj'
    exact ((mem_supp x j).mp (hsub ((mem_supp y j).mpr hj'))) hj
  have hsmall : supp (x - t • y) ⊆ supp x := by
    intro j hj
    apply (mem_supp x j).mpr
    intro hxj
    have hyj := hzero j hxj
    have hneq := (mem_supp (x - t • y) j).mp hj
    apply hneq
    change x j - t * y j = 0
    rw [hxj, hyj]
    ring
  have hiout : i ∉ supp (x - t • y) := by
    intro hi'
    have hneq := (mem_supp (x - t • y) i).mp hi'
    apply hneq
    change x i - t * y i = 0
    linarith
  refine ⟨t, ht, hz, Finset.ssubset_iff_subset_ne.mpr ⟨hsmall, ?_⟩⟩
  intro heq
  apply hiout
  rw [heq]
  exact (mem_supp x i).mpr (ne_of_gt hxi)

/-- A positive circuit has only one nonnegative null ray on its support. -/
theorem same_support_ray {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (x y : Fin n → ℝ) (hx : Circuit A x) (hy : NonnegNull A y)
    (hyne : y ≠ 0) (hsub : supp y ⊆ supp x) :
    ∃ t : ℝ, 0 < t ∧ x = t • y := by
  classical
  obtain ⟨t, ht, hz, hstrict⟩ :=
    prune x y hx.1.1 hsub (positive_coordinate y hy.1 hyne)
  have hzA : A (x - t • y) = 0 := by
    simp [map_sub, map_smul, hx.1.2, hy.2]
  have heq : x - t • y = 0 := by
    by_contra hne
    have hback := hx.2.2 (x - t • y) ⟨hz, hzA⟩ hne (Finset.ssubset_iff_subset_ne.mp hstrict).1
    have hle := Finset.card_le_card hback
    have hlt := Finset.card_lt_card hstrict
    omega
  exact ⟨t, ht, sub_eq_zero.mp heq⟩

/-- Scalar normalization preserves the exact support. -/
theorem supp_smul {n : ℕ} (t : ℝ) (ht : t ≠ 0) (x : Fin n → ℝ) :
    supp (t • x) = supp x := by
  classical
  ext i
  simp only [mem_supp, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h hx
    exact h (by rw [hx, mul_zero])
  · intro h
    exact mul_ne_zero ht h

/-- Nonzero nonnegative vectors have positive total mass. -/
private theorem mass_pos {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) : 0 < ∑ i, x i := by
  obtain ⟨j, hj⟩ := positive_coordinate x hx hne
  exact hj.trans_le (Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ j))

/-- Exact normalization of an arbitrary nonnegative null vector. -/
private theorem normalize_null {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hx : NonnegNull A x) (hne : x ≠ 0) :
    NonnegNull A ((∑ i, x i)⁻¹ • x) ∧
      (∑ i, ((∑ j, x j)⁻¹ • x) i) = 1 := by
  have hm := mass_pos x hx.1 hne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    exact mul_nonneg (inv_pos.mpr hm).le (hx.1 i)
  · simp [map_smul, hx.2]
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hm)

/-- Positive circuit rays become actual extreme points after sum-one
normalization. The proof uses Mathlib's geometric open-segment definition. -/
theorem extreme_of_normalized_circuit {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hx : Circuit A x) (hm : (∑ i, x i) = 1) :
    x ∈ Set.extremePoints ℝ
      {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ A z = 0 ∧ (∑ i, z i) = 1} := by
  classical
  refine ⟨⟨hx.1.1, hx.1.2, hm⟩, ?_⟩
  intro y hy z hz hseg
  obtain ⟨α, β, hα, hβ, hab, heq⟩ := hseg
  have hsub : supp y ⊆ supp x := by
    intro i hi
    apply (mem_supp x i).mpr
    intro hxi
    have hyi : 0 < y i := lt_of_le_of_ne (hy.1 i) (Ne.symm ((mem_supp y i).mp hi))
    have hpos := mul_pos hα hyi
    have hnon := mul_nonneg hβ.le (hz.1 i)
    have h := congrFun heq i
    change α * y i + β * z i = x i at h
    rw [hxi] at h
    linarith
  have hyne : y ≠ 0 := by
    intro h
    simpa [h] using hy.2.2
  obtain ⟨t, ht, hxy⟩ := same_support_ray A x y hx ⟨hy.1, hy.2.1⟩ hyne hsub
  have hmass := congrArg (fun v : Fin n → ℝ => ∑ i, v i) hxy
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hm, hy.2.2, mul_one] at hmass
  have hxy' : x = y := by simpa only [← hmass, one_smul] using hxy
  exact hxy'.symm

/-- Every extreme point of the normalized nonnegative kernel has support
minimal among ALL nonzero nonnegative null vectors. -/
theorem circuit_of_normalized_extreme {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hx : x ∈ Set.extremePoints ℝ
      {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ A z = 0 ∧ (∑ i, z i) = 1}) :
    Circuit A x := by
  classical
  have hxne : x ≠ 0 := by
    intro h
    simpa [h] using hx.1.2.2
  refine ⟨⟨hx.1.1, hx.1.2.1⟩, hxne, ?_⟩
  intro y hy hyne hyx
  obtain ⟨t, ht, hr, hstrict⟩ :=
    prune x y hx.1.1 hyx (positive_coordinate y hy.1 hyne)
  let r : Fin n → ℝ := x - t • y
  have hrA : A r = 0 := by
    simp [r, map_sub, map_smul, hx.1.2.1, hy.2]
  by_cases hr0 : r = 0
  · have hxy : x = t • y := sub_eq_zero.mp hr0
    simpa only [hxy, supp_smul t (ne_of_gt ht)] using
      (show supp y ⊆ supp y from fun _ hi => hi)
  · have hypos := mass_pos y hy.1 hyne
    have hrpos := mass_pos r hr hr0
    let cy : Fin n → ℝ := (∑ i, y i)⁻¹ • y
    let cr : Fin n → ℝ := (∑ i, r i)⁻¹ • r
    have hcy := normalize_null A y hy hyne
    have hcr := normalize_null A r ⟨hr, hrA⟩ hr0
    have hcyK : cy ∈ {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ A z = 0 ∧ (∑ i, z i) = 1} :=
      ⟨hcy.1.1, hcy.1.2, hcy.2⟩
    have hcrK : cr ∈ {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ A z = 0 ∧ (∑ i, z i) = 1} :=
      ⟨hcr.1.1, hcr.1.2, hcr.2⟩
    have hsum : t * (∑ i, y i) + (∑ i, r i) = 1 := by
      dsimp only [r]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum, hx.1.2.2]
      ring
    have hcancel : (t * (∑ i, y i)) * (∑ i, y i)⁻¹ = t := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hypos), mul_one]
    have hcomb : (t * (∑ i, y i)) • cy + (∑ i, r i) • cr = x := by
      dsimp only [cy, cr]
      rw [smul_smul, smul_smul, hcancel, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]
      dsimp only [r]
      module
    have hseg : x ∈ openSegment ℝ cy cr :=
      ⟨t * (∑ i, y i), (∑ i, r i), mul_pos ht hypos, hrpos, hsum, hcomb⟩
    have hxe : cy = x := hx.2 hcyK hcrK hseg
    rw [← hxe]
    change supp ((∑ i, y i)⁻¹ • y) ⊆ supp y
    simpa only [supp_smul _ (ne_of_gt (inv_pos.mpr hypos))] using
      (show supp y ⊆ supp y from fun _ hi => hi)

/-- Normalized positive-circuit representatives are unique on their support. -/
theorem normalized_ray_unique {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (x y : Fin n → ℝ) (hx : Circuit A x) (hy : NonnegNull A y)
    (hsub : supp y ⊆ supp x) (hsx : (∑ i, x i) = 1)
    (hsy : (∑ i, y i) = 1) : x = y := by
  have hyne : y ≠ 0 := by intro h; simp [h] at hsy
  obtain ⟨t, ht, heq⟩ := same_support_ray A x y hx hy hyne hsub
  have hm := congrArg (fun z : Fin n → ℝ => ∑ i, z i) heq
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hsx, hsy, mul_one] at hm
  simpa only [← hm, one_smul] using heq

end Hirsch.PositiveCircuitTests

/-- The canonical objects computed by exact normalized-kernel vertex
enumeration are precisely the normalized positive circuits. No RREF,
feasibility, vertex-enumeration or catalogue-completeness oracle is assumed. -/
theorem solution (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ) :
    (x ∈ Set.extremePoints ℝ
      {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ A z = 0 ∧ (∑ i, z i) = 1}) ↔
      ((∀ i, 0 ≤ x i) ∧ A x = 0 ∧ (∑ i, x i) = 1 ∧
        (∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
          Function.support y ⊆ Function.support x →
          Function.support x ⊆ Function.support y)) := by
  classical
  constructor
  · intro hx
    have hc := Hirsch.PositiveCircuitTests.circuit_of_normalized_extreme A x hx
    refine ⟨hx.1.1, hx.1.2.1, hx.1.2.2, ?_⟩
    intro y hy hyA hyne hyx i hi
    have hsub : Hirsch.PositiveCircuitTests.supp y ⊆ Hirsch.PositiveCircuitTests.supp x := by
      intro j hj
      exact (Hirsch.PositiveCircuitTests.mem_supp x j).mpr
        (hyx ((Hirsch.PositiveCircuitTests.mem_supp y j).mp hj))
    exact (Hirsch.PositiveCircuitTests.mem_supp y i).mp
      (hc.2.2 y ⟨hy, hyA⟩ hyne hsub ((Hirsch.PositiveCircuitTests.mem_supp x i).mpr hi))
  · rintro ⟨hx, hAx, hsum, hminimal⟩
    have hxne : x ≠ 0 := by intro h; simp [h] at hsum
    apply Hirsch.PositiveCircuitTests.extreme_of_normalized_circuit A x ?_ hsum
    refine ⟨⟨hx, hAx⟩, hxne, ?_⟩
    intro y hy hyne hyx i hi
    have hsub : Function.support y ⊆ Function.support x := by
      intro j hj
      exact (Hirsch.PositiveCircuitTests.mem_supp x j).mp
        (hyx ((Hirsch.PositiveCircuitTests.mem_supp y j).mpr hj))
    exact (Hirsch.PositiveCircuitTests.mem_supp y i).mpr
      (hminimal y hy.1 hy.2 hyne hsub ((Hirsch.PositiveCircuitTests.mem_supp x i).mp hi))

#print axioms Hirsch.PositiveCircuitTests.extreme_of_normalized_circuit
#print axioms Hirsch.PositiveCircuitTests.circuit_of_normalized_extreme
#print axioms Hirsch.PositiveCircuitTests.normalized_ray_unique
#print axioms solution
