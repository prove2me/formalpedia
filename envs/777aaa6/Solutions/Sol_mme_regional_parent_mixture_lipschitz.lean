-- Prove2me | solution 1 for mme_regional_parent_mixture_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T21:17:33.593062+00:00
-- url     : https://prove2.me/submissions/4f7079c8-0666-4399-b6b8-108bce844808

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib
open BigOperators MME MME.RegionRealization MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem freq_bounds {C W : Type*} [Fintype W]
    (mu : C → W → ℕ) (c : C) (w : W) : cellFrequency mu c w ∈ Set.Icc 0 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · by_cases hz : ∑ v, mu c v = 0
    · simp [cellFrequency,hz]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))).mpr
      exact_mod_cast Finset.single_le_sum (f := mu c) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)

private theorem product_close (a b c d delta : ℝ)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hdelta : 0 ≤ delta)
    (hac : |a-c| ≤ delta) (hbd : |b-d| ≤ delta) : |a*b-c*d| ≤ 2*delta := by
  calc
    |a*b-c*d| = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| * b+c * |b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg hb.1,abs_of_nonneg hc.1]
    _ ≤ delta*1+1*delta := add_le_add
      (mul_le_mul hac hb.2 hb.1 hdelta) (mul_le_mul hc.2 hbd (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem solution {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (hmass : ∀ r, ∑ c, m r c = n r)
    (mu nu : Cell half R parent → W → ℕ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hclose : ∀ c w, |cellFrequency mu c w - cellFrequency nu c w| ≤ delta) :
    (∀ r w, |parentMixture htotal n m mu r w - parentMixture htotal n m nu r w| ≤ 2*delta) ∧
    (∀ (eps : ℝ) (f : Position n → W), parentTypical htotal n m mu eps f →
      parentTypical htotal n m nu (eps+2*delta) f) := by
  classical
  have hmix (r : Fin R) (w : Fin 2 → W) :
      |parentMixture htotal n m mu r w - parentMixture htotal n m nu r w| ≤ 2*delta := by
    by_cases hn : n r = 0
    · simp [parentMixture,hn,hdelta]
    have hnR : 0 < (n r : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    unfold parentMixture
    rw [← sub_div,abs_div,abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ c, |(m r c : ℝ) * cellFrequency mu ⟨r,c⟩ (w 0) *
            cellFrequency mu ⟨r,complement (htotal r) c⟩ (w 1) -
          (m r c : ℝ) * cellFrequency nu ⟨r,c⟩ (w 0) *
            cellFrequency nu ⟨r,complement (htotal r) c⟩ (w 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, (m r c : ℝ) * (2*delta) := by
        apply Finset.sum_le_sum
        intro c _
        have hp := product_close _ _ _ _ delta
          (freq_bounds mu ⟨r,complement (htotal r) c⟩ (w 1))
          (freq_bounds nu ⟨r,c⟩ (w 0)) hdelta (hclose ⟨r,c⟩ (w 0))
          (hclose ⟨r,complement (htotal r) c⟩ (w 1))
        rw [show (m r c : ℝ) * cellFrequency mu ⟨r,c⟩ (w 0) *
            cellFrequency mu ⟨r,complement (htotal r) c⟩ (w 1) -
          (m r c : ℝ) * cellFrequency nu ⟨r,c⟩ (w 0) *
            cellFrequency nu ⟨r,complement (htotal r) c⟩ (w 1) =
          (m r c : ℝ) * (cellFrequency mu ⟨r,c⟩ (w 0) *
            cellFrequency mu ⟨r,complement (htotal r) c⟩ (w 1) -
          cellFrequency nu ⟨r,c⟩ (w 0) *
            cellFrequency nu ⟨r,complement (htotal r) c⟩ (w 1)) by ring,
          abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
      _ = 2*delta*(n r : ℝ) := by
        rw [← Finset.sum_mul,← Nat.cast_sum,hmass]
        ring
  refine ⟨hmix,?_⟩
  intro eps f hf r w
  exact (abs_sub_le _ _ _).trans_lt (add_lt_add_of_lt_of_le (hf r w) (hmix r w))
