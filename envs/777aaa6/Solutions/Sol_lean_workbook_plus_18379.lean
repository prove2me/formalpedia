-- Prove2me | solution 1 for lean_workbook_plus_18379
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:12:52.353067+00:00
-- url     : https://prove2.me/submissions/4cd3b8ff-84e5-48ae-b7b8-b5c0e8ac45e3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace CubicSphereRadicalBound

-- The weighted-square Schur certificate is reused from workbook59379.
theorem schur_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
  by_cases hs : a + b + c = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [ha0, hb0, hc0]
  · have hs0 : 0 < a + b + c := lt_of_le_of_ne (by positivity) (Ne.symm hs)
    have hf : 0 < a + (b + c) / 4 := by linarith
    have hp : 0 ≤ (a + (b + c) / 4) *
        (a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b)) := by
      calc
        0 ≤ b * c * (b - c) ^ 2 +
            (c * a * (c - a) ^ 2 + a * b * (a - b) ^ 2) / 4 +
            (2 * a ^ 2 - b ^ 2 - c ^ 2 - a * b + 2 * b * c - c * a) ^ 2 / 4 := by
          positivity
        _ = _ := by ring
    exact nonneg_of_mul_nonneg_right hp hf

theorem constraint_schur (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    0 ≤ (9 - 2 * (a + b + c)) * (a * b * c) - (a + b + c) ^ 3 +
      8 * (a + b + c) := by
  have hs := schur_nonneg a b c ha hb hc
  have hz : (2 * (a + b + c)) * (a ^ 2 + b ^ 2 + c ^ 2 + a * b * c - 4) = 0 := by
    rw [h, sub_self, mul_zero]
  nlinarith

-- These sum and product constraints were already established in 59379 and 76084.
theorem constraint_sum (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) : a + b + c ≤ 3 := by
  let s := a + b + c
  let p := a * b * c
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hv : 0 ≤ 12 - 3 * p - s ^ 2 := by
    dsimp [p, s]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hs4 : s < 4 := by nlinarith
  have hschur := constraint_schur a b c ha hb hc h
  change 0 ≤ (9 - 2 * s) * p - s ^ 3 + 8 * s at hschur
  have hm := mul_nonneg (show 0 ≤ 9 - 2 * s by linarith) hv
  have hcubic : 0 ≤ 108 - 9 * s ^ 2 - s ^ 3 := by nlinarith
  by_contra! hs
  have hp := mul_pos (show 0 < s - 3 by linarith)
    (show 0 < s ^ 2 + 12 * s + 36 by positivity)
  nlinarith

theorem constraint_product (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) : 0 < a * b * c ∧ a * b * c ≤ 1 := by
  have hf : (c + 2) * (a * b + c - 2) ≤ 0 := by
    nlinarith only [h, sq_nonneg (a - b)]
  have hab : a * b + c - 2 ≤ 0 := by
    by_contra! hh
    have hp := mul_pos (show 0 < c + 2 by linarith) hh
    linarith
  have hm := mul_le_mul_of_nonneg_right hab hc.le
  exact ⟨by positivity, by nlinarith only [hm, sq_nonneg (c - 1)]⟩

theorem constraint_sum_eq (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    a + b + c = 3 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro hs
    have hp := constraint_schur a b c ha hb hc h
    rw [hs] at hp
    have hq : a ^ 2 + b ^ 2 + c ^ 2 ≤ 3 := by nlinarith
    have ha2 : (a - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have hb2 : (b - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have hc2 : (c - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp ha2),
      sub_eq_zero.mp (sq_eq_zero_iff.mp hb2), sub_eq_zero.mp (sq_eq_zero_iff.mp hc2)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

def gap (p r : ℝ) : ℝ := 8 - 4 * r - (p - r) ^ 2

theorem gap_interpolation (p l r : ℝ) :
    (1 - l) * gap p r = (1 - r) * gap p l + (r - l) * gap p 1 +
      (r - l) * (1 - r) * (1 - l) := by
  unfold gap
  ring

theorem gap_interval_pos (p l r : ℝ) (hl : l < 1) (hlr : l ≤ r) (hr : r ≤ 1)
    (hleft : 0 < gap p l) (hright : 0 < gap p 1) : 0 < gap p r := by
  have ha := mul_nonneg (show 0 ≤ 1 - r by linarith) hleft.le
  have hb := mul_nonneg (sub_nonneg.mpr hlr) hright.le
  have hc := mul_nonneg (mul_nonneg (sub_nonneg.mpr hlr)
    (show 0 ≤ 1 - r by linarith)) (show 0 ≤ 1 - l by linarith)
  have hid := gap_interpolation p l r
  have hpos : 0 < (1 - l) * gap p r := by
    by_cases he : r = l
    · subst r
      exact mul_pos (by linarith) hleft
    · have hprod := mul_pos (sub_pos.mpr (lt_of_le_of_ne hlr (Ne.symm he))) hright
      linarith
  exact pos_of_mul_pos_right hpos (by linarith)

theorem gap_endpoint (p : ℝ) (hd : 9 - 2 * p ≠ 0) :
    gap p (p * (p ^ 2 - 8) / (9 - 2 * p)) * (9 - 2 * p) ^ 2 =
      (3 - p) * (p ^ 2 - 8) * (p ^ 3 + 7 * p ^ 2 - 9 * p - 27) := by
  have hid (l d : ℝ) : gap p l * d ^ 2 =
      8 * d ^ 2 - 4 * (l * d) * d - (p * d - l * d) ^ 2 := by
    unfold gap
    ring
  rw [hid, div_mul_cancel₀ _ hd]
  ring

theorem scalar_gap_pos (p r : ℝ) (hp : 0 ≤ p) (hp3 : p < 3)
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 ≤ (9 - 2 * p) * r - p ^ 3 + 8 * p) : 0 < gap p r := by
  have hg1 : 0 < gap p 1 := by
    have hm := mul_pos (show 0 < 3 - p by linarith) (show 0 < p + 1 by linarith)
    dsimp [gap]
    nlinarith
  by_cases hp8 : p ^ 2 ≤ 8
  · have hg0 : 0 ≤ gap p 0 := by dsimp [gap]; nlinarith
    have ha := mul_nonneg (show 0 ≤ 1 - r by linarith) hg0
    have hb := mul_pos hr0 hg1
    have hc := mul_nonneg hr0.le (show 0 ≤ 1 - r by linarith)
    have hid := gap_interpolation p 0 r
    nlinarith
  · have hp8 : 8 < p ^ 2 := lt_of_not_ge hp8
    let l := p * (p ^ 2 - 8) / (9 - 2 * p)
    have hd : 0 < 9 - 2 * p := by linarith
    have hlr : l ≤ r := by
      apply (div_le_iff₀ hd).2
      nlinarith
    have hl1 : l < 1 := by
      apply (div_lt_iff₀ hd).2
      have hm := mul_pos (show 0 < 3 - p by linarith)
        (show 0 < p ^ 2 + 3 * p + 3 by positivity)
      nlinarith
    have hf : 0 < p ^ 3 + 7 * p ^ 2 - 9 * p - 27 := by
      have hc : 0 ≤ p ^ 3 := pow_nonneg hp 3
      nlinarith
    have hprod := mul_pos (mul_pos (show 0 < 3 - p by linarith)
      (show 0 < p ^ 2 - 8 by linarith)) hf
    have hid := gap_endpoint p (ne_of_gt hd)
    have hgl : 0 < gap p l := by
      apply pos_of_mul_pos_left (b := (9 - 2 * p) ^ 2)
      · change 0 < gap p (p * (p ^ 2 - 8) / (9 - 2 * p)) * (9 - 2 * p) ^ 2
        rw [hid]
        exact hprod
      · positivity
    exact gap_interval_pos p l r hl1 hlr hr1 hgl hg1

theorem source_strict (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) (hne : ¬ (a = 1 ∧ b = 1 ∧ c = 1)) :
    a + b + c < 2 * Real.sqrt (2 - a * b * c) + a * b * c := by
  have hp := constraint_product a b c ha hb hc h
  have hs := constraint_sum a b c ha.le hb.le hc.le h
  have hsne : a + b + c ≠ 3 := by
    intro he
    exact hne ((constraint_sum_eq a b c ha.le hb.le hc.le h).mp he)
  have hg := scalar_gap_pos (a + b + c) (a * b * c) (by positivity)
    (lt_of_le_of_ne hs hsne) hp.1 hp.2 (constraint_schur a b c ha.le hb.le hc.le h)
  have hrad : 0 ≤ 2 - a * b * c := by linarith
  have hsq := Real.sq_sqrt hrad
  have hnon := Real.sqrt_nonneg (2 - a * b * c)
  dsimp [gap] at hg
  nlinarith

theorem source_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    a + b + c ≤ 2 * Real.sqrt (2 - a * b * c) + a * b * c := by
  by_cases he : a = 1 ∧ b = 1 ∧ c = 1
  · rcases he with ⟨rfl, rfl, rfl⟩
    norm_num
  · exact (source_strict a b c ha hb hc h he).le

theorem source_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    a + b + c = 2 * Real.sqrt (2 - a * b * c) + a * b * c ↔
      a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro he
    by_contra hn
    exact (ne_of_lt (source_strict a b c ha hb hc h hn)) he
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

end CubicSphereRadicalBound

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_habc : a * b * c = 1) (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    2 * Real.sqrt (2 - a * b * c) + a * b * c ≥ a + b + c :=
  CubicSphereRadicalBound.source_bound a b c ha hb hc h

#print axioms CubicSphereRadicalBound.schur_nonneg
#print axioms CubicSphereRadicalBound.constraint_schur
#print axioms CubicSphereRadicalBound.constraint_sum
#print axioms CubicSphereRadicalBound.constraint_product
#print axioms CubicSphereRadicalBound.constraint_sum_eq
#print axioms CubicSphereRadicalBound.gap
#print axioms CubicSphereRadicalBound.gap_interpolation
#print axioms CubicSphereRadicalBound.gap_interval_pos
#print axioms CubicSphereRadicalBound.gap_endpoint
#print axioms CubicSphereRadicalBound.scalar_gap_pos
#print axioms CubicSphereRadicalBound.source_strict
#print axioms CubicSphereRadicalBound.source_bound
#print axioms CubicSphereRadicalBound.source_equality
#print axioms solution
