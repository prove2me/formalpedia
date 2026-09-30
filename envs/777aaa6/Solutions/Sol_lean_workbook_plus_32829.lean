-- Prove2me | solution 1 for lean_workbook_plus_32829
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:48:39.764716+00:00
-- url     : https://prove2.me/submissions/7d562bc5-63f3-47e3-ab65-e5500518c360

import Mathlib

namespace WeightedCyclicProductMinimum

noncomputable def cyclicGap (a b c : ℝ) : ℝ :=
  a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3 * a * b * c

noncomputable def ratio (k a b c : ℝ) : ℝ :=
  (a + k * b) * (b + k * c) * (c + k * a) / (a * b * c)

noncomputable def value (n : ℕ) (k a b c : ℝ) : ℝ :=
  (ratio k (a ^ n) (b ^ n) (c ^ n)) ^ ((3 : ℝ)⁻¹)

def attainable (n : ℕ) (k : ℝ) : Set ℝ :=
  {v | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ value n k a b c = v}

theorem ordered_cyclic_gap (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
    0 ≤ cyclicGap a b c := by
  have hq : 0 ≤ (a - c) ^ 2 + (b - c) ^ 2 - (a - c) * (b - c) := by
    nlinarith only [sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a - b)]
  have hi : cyclicGap a b c =
      c * ((a - c) ^ 2 + (b - c) ^ 2 - (a - c) * (b - c)) +
        (a - c) ^ 2 * (b - c) := by
    unfold cyclicGap
    ring
  rw [hi]
  exact add_nonneg (mul_nonneg hc hq) (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hcb))

theorem cyclic_gap_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ cyclicGap a b c := by
  by_cases hab : a ≤ b
  · by_cases hac : a ≤ c
    · have h := ordered_cyclic_gap b c a ha hab hac
      unfold cyclicGap at h ⊢
      nlinarith only [h]
    · exact ordered_cyclic_gap a b c hc (le_of_lt (lt_of_not_ge hac))
        ((le_of_lt (lt_of_not_ge hac)).trans hab)
  · by_cases hbc : b ≤ c
    · have h := ordered_cyclic_gap c a b hb hbc (le_of_lt (lt_of_not_ge hab))
      unfold cyclicGap at h ⊢
      nlinarith only [h]
    · exact ordered_cyclic_gap a b c hc
        ((le_of_lt (lt_of_not_ge hbc)).trans (le_of_lt (lt_of_not_ge hab)))
        (le_of_lt (lt_of_not_ge hbc))

theorem product_gap_identity (k a b c : ℝ) :
    (a + k * b) * (b + k * c) * (c + k * a) - (1 + k) ^ 3 * (a * b * c) =
      k * cyclicGap a b c + k ^ 2 * cyclicGap b a c := by
  unfold cyclicGap
  ring

theorem ratio_pos (k a b c : ℝ) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < ratio k a b c := by
  unfold ratio
  positivity

theorem ratio_bound (k a b c : ℝ) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1 + k) ^ 3 ≤ ratio k a b c := by
  have h1 := cyclic_gap_nonneg a b c ha.le hb.le hc.le
  have h2 := cyclic_gap_nonneg b a c hb.le ha.le hc.le
  have h := add_nonneg (mul_nonneg hk.le h1) (mul_nonneg (sq_nonneg k) h2)
  rw [← product_gap_identity] at h
  unfold ratio
  apply (le_div_iff₀ (mul_pos (mul_pos ha hb) hc)).mpr
  exact sub_nonneg.mp h

theorem ratio_equality_iff (k a b c : ℝ) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ratio k a b c = (1 + k) ^ 3 ↔ a = b ∧ b = c := by
  constructor
  · intro he
    have hp := (div_eq_iff (ne_of_gt (mul_pos (mul_pos ha hb) hc))).mp he
    have h1 := cyclic_gap_nonneg a b c ha.le hb.le hc.le
    have h2 := cyclic_gap_nonneg b a c hb.le ha.le hc.le
    have hk1 := mul_nonneg hk.le h1
    have hk2 := mul_nonneg (sq_nonneg k) h2
    have hs : k * cyclicGap a b c + k ^ 2 * cyclicGap b a c = 0 := by
      rw [← product_gap_identity, hp]
      ring
    have hz1 : k * cyclicGap a b c = 0 := by linarith only [hs, hk1, hk2]
    have hz2 : k ^ 2 * cyclicGap b a c = 0 := by linarith only [hs, hk1, hk2]
    have hg1 := (mul_eq_zero.mp hz1).resolve_left (ne_of_gt hk)
    have hg2 := (mul_eq_zero.mp hz2).resolve_left (pow_ne_zero 2 (ne_of_gt hk))
    have hsq : c * (a - b) ^ 2 + a * (b - c) ^ 2 + b * (c - a) ^ 2 = 0 := by
      unfold cyclicGap at hg1 hg2
      linear_combination hg1 + hg2
    have hab0 := mul_nonneg hc.le (sq_nonneg (a - b))
    have hbc0 := mul_nonneg ha.le (sq_nonneg (b - c))
    have hca0 := mul_nonneg hb.le (sq_nonneg (c - a))
    have habz : c * (a - b) ^ 2 = 0 := by linarith only [hsq, hab0, hbc0, hca0]
    have hbcz : a * (b - c) ^ 2 = 0 := by linarith only [hsq, hab0, hbc0, hca0]
    have habsq := (mul_eq_zero.mp habz).resolve_left (ne_of_gt hc)
    have hbcsq := (mul_eq_zero.mp hbcz).resolve_left (ne_of_gt ha)
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp habsq), sub_eq_zero.mp (sq_eq_zero_iff.mp hbcsq)⟩
  · rintro ⟨rfl, rfl⟩
    unfold ratio
    field_simp [ne_of_gt hc]
    <;> ring

theorem root_lower_bound (n : ℕ) (k a b c : ℝ) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 + k ≤ value n k a b c := by
  have h := ratio_bound k (a ^ n) (b ^ n) (c ^ n) hk (pow_pos ha n) (pow_pos hb n) (pow_pos hc n)
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (1 + k) ^ 3) h
    (by positivity : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
  have hi : ((1 + k) ^ 3 : ℝ) ^ ((3 : ℝ)⁻¹) = 1 + k :=
    Real.pow_rpow_inv_natCast (by linarith) (by decide : (3 : ℕ) ≠ 0)
  rw [hi] at hr
  exact hr

theorem root_equality_iff (n : ℕ) (hn : n ≠ 0) (k a b c : ℝ) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    value n k a b c = 1 + k ↔ a = b ∧ b = c := by
  have hr := ratio_pos k (a ^ n) (b ^ n) (c ^ n) hk (pow_pos ha n) (pow_pos hb n) (pow_pos hc n)
  have hcube : (value n k a b c) ^ 3 = ratio k (a ^ n) (b ^ n) (c ^ n) :=
    Real.rpow_inv_natCast_pow hr.le (by decide : (3 : ℕ) ≠ 0)
  calc
    value n k a b c = 1 + k ↔ ratio k (a ^ n) (b ^ n) (c ^ n) = (1 + k) ^ 3 := by
      constructor
      · intro he
        rw [he] at hcube
        exact hcube.symm
      · intro he
        unfold value
        rw [he]
        exact Real.pow_rpow_inv_natCast (by linarith) (by decide : (3 : ℕ) ≠ 0)
    _ ↔ a ^ n = b ^ n ∧ b ^ n = c ^ n :=
      ratio_equality_iff k (a ^ n) (b ^ n) (c ^ n) hk (pow_pos ha n) (pow_pos hb n) (pow_pos hc n)
    _ ↔ a = b ∧ b = c := and_congr (pow_left_inj₀ ha.le hb.le hn) (pow_left_inj₀ hb.le hc.le hn)

theorem diagonal_model (n : ℕ) (k t : ℝ) (hk : 0 < k) (ht : 0 < t) :
    value n k t t t = 1 + k := by
  have he := (ratio_equality_iff k (t ^ n) (t ^ n) (t ^ n) hk
    (pow_pos ht n) (pow_pos ht n) (pow_pos ht n)).mpr ⟨rfl, rfl⟩
  unfold value
  rw [he]
  exact Real.pow_rpow_inv_natCast (by linarith) (by decide : (3 : ℕ) ≠ 0)

theorem minimum (n : ℕ) (k : ℝ) (hk : 0 < k) : IsLeast (attainable n k) (1 + k) := by
  refine ⟨⟨1, 1, 1, by norm_num, by norm_num, by norm_num, diagonal_model n k 1 hk (by norm_num)⟩, ?_⟩
  rintro v ⟨a, b, c, ha, hb, hc, rfl⟩
  exact root_lower_bound n k a b c hk ha hb hc

theorem source_minimum : IsLeast (attainable 2008 2007) 2008 := by
  have h := minimum 2008 2007 (by norm_num)
  convert h using 1 <;> ring

theorem source_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    value 2008 2007 a b c = 2008 ↔ a = b ∧ b = c := by
  have h := root_equality_iff 2008 (by decide) 2007 a b c (by norm_num) ha hb hc
  convert h using 1 <;> ring

end WeightedCyclicProductMinimum

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2008 + 2007 * b ^ 2008) * (b ^ 2008 + 2007 * c ^ 2008) *
      (c ^ 2008 + 2007 * a ^ 2008) / (a ^ 2008 * b ^ 2008 * c ^ 2008) ≥ 2008 := by
  have h := WeightedCyclicProductMinimum.ratio_bound 2007 (a ^ 2008) (b ^ 2008) (c ^ 2008)
    (by norm_num) (pow_pos ha 2008) (pow_pos hb 2008) (pow_pos hc 2008)
  exact (show (2008 : ℝ) ≤ (1 + 2007) ^ 3 by norm_num).trans h

#print axioms WeightedCyclicProductMinimum.ordered_cyclic_gap
#print axioms WeightedCyclicProductMinimum.cyclic_gap_nonneg
#print axioms WeightedCyclicProductMinimum.product_gap_identity
#print axioms WeightedCyclicProductMinimum.ratio_pos
#print axioms WeightedCyclicProductMinimum.ratio_bound
#print axioms WeightedCyclicProductMinimum.ratio_equality_iff
#print axioms WeightedCyclicProductMinimum.root_lower_bound
#print axioms WeightedCyclicProductMinimum.root_equality_iff
#print axioms WeightedCyclicProductMinimum.diagonal_model
#print axioms WeightedCyclicProductMinimum.minimum
#print axioms WeightedCyclicProductMinimum.source_minimum
#print axioms WeightedCyclicProductMinimum.source_equality
#print axioms solution
