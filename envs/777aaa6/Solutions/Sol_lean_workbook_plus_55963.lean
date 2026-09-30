-- Prove2me | solution 1 for lean_workbook_plus_55963
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:53:52.034417+00:00
-- url     : https://prove2.me/submissions/0378a233-ad62-4c88-a20a-8537a0c17f71

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

def cyclicNumerator {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 2 * b ^ 2 * (b - c) * (b + c) * (c + a) +
    b ^ 2 * c ^ 2 * (c - a) * (c + a) * (a + b) +
    c ^ 2 * a ^ 2 * (a - b) * (a + b) * (b + c)

theorem numerator_rotate {R : Type*} [CommRing R] (a b c : R) :
    cyclicNumerator a b c = cyclicNumerator b c a := by unfold cyclicNumerator; ring

theorem shifted_identity {R : Type*} [CommRing R] (x y z : R) :
    cyclicNumerator (z + x) (z + y) z - 3 * z ^ 5 * (x ^ 2 + y ^ 2) =
      3 * z ^ 5 * (x - y) ^ 2 +
      z ^ 4 * (7 * x ^ 3 + 9 * x * y ^ 2 + 7 * y ^ 3) +
      z ^ 3 * (2 * x ^ 4 + 4 * x ^ 3 * y + 10 * x ^ 2 * y ^ 2 +
        16 * x * y ^ 3 + 2 * y ^ 4) +
      z ^ 2 * (x ^ 4 * y + 4 * x ^ 3 * y ^ 2 + 14 * x ^ 2 * y ^ 3 + 5 * x * y ^ 4) +
      4 * z * x ^ 2 * y ^ 3 * (x + y) + x ^ 3 * y ^ 4 := by
  unfold cyclicNumerator
  ring

theorem shifted_bound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * z ^ 5 * (x ^ 2 + y ^ 2) ≤ cyclicNumerator (z + x) (z + y) z := by
  rw [← sub_nonneg, shifted_identity]
  positivity

theorem minimum_bound (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
    3 * c ^ 5 * ((a - c) ^ 2 + (b - c) ^ 2) ≤ cyclicNumerator a b c := by
  have h := shifted_bound (a - c) (b - c) c (sub_nonneg.mpr hca) (sub_nonneg.mpr hcb) hc
  have ha : c + (a - c) = a := by ring
  have hb : c + (b - c) = b := by ring
  simpa only [ha, hb] using h

theorem minimum_properties (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hca : c ≤ a) (hcb : c ≤ b) :
    0 ≤ cyclicNumerator a b c ∧
      (cyclicNumerator a b c = 0 → a = b ∧ b = c) := by
  have h := minimum_bound a b c (le_of_lt hc) hca hcb
  have hn : 0 ≤ 3 * c ^ 5 * ((a - c) ^ 2 + (b - c) ^ 2) := by positivity
  refine ⟨le_trans hn h, ?_⟩
  intro he
  have hprod : (3 * c ^ 5) * ((a - c) ^ 2 + (b - c) ^ 2) ≤ (3 * c ^ 5) * 0 := by
    nlinarith [h]
  have hs := (mul_le_mul_iff_right₀ (show 0 < 3 * c ^ 5 by positivity)).mp hprod
  have he1 : (a - c) ^ 2 = 0 := by nlinarith [sq_nonneg (a - c), sq_nonneg (b - c)]
  have he2 : (b - c) ^ 2 = 0 := by nlinarith [sq_nonneg (a - c), sq_nonneg (b - c)]
  have h1 := sq_eq_zero_iff.mp he1
  have h2 := sq_eq_zero_iff.mp he2
  constructor <;> linarith

theorem numerator_properties (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ cyclicNumerator a b c ∧
      (cyclicNumerator a b c = 0 → a = b ∧ b = c) := by
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · have h := minimum_properties b c a hb hc ha hab hac
      refine ⟨?_, ?_⟩
      · simpa only [numerator_rotate a b c] using h.1
      · intro he
        have hzero : cyclicNumerator b c a = 0 := by
          simpa only [numerator_rotate a b c] using he
        obtain ⟨h1, h2⟩ := h.2 hzero
        constructor <;> linarith
    · exact minimum_properties a b c ha hb hc hca (le_trans hca hab)
  · rcases le_total b c with hbc | hcb
    · have h := minimum_properties c a b hc ha hb hbc hba
      have hr : cyclicNumerator a b c = cyclicNumerator c a b := by
        rw [numerator_rotate a b c, numerator_rotate b c a]
      refine ⟨?_, ?_⟩
      · simpa only [hr] using h.1
      · intro he
        have hzero : cyclicNumerator c a b = 0 := by simpa only [hr] using he
        obtain ⟨h1, h2⟩ := h.2 hzero
        constructor <;> linarith
    · exact minimum_properties a b c ha hb hc (le_trans hcb hba) hcb

noncomputable def cyclicSum (a b c : ℝ) : ℝ :=
  a ^ 2 * b ^ 2 * (b - c) / (a + b) + b ^ 2 * c ^ 2 * (c - a) / (b + c) +
    c ^ 2 * a ^ 2 * (a - b) / (c + a)

theorem denominator_identity (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    cyclicSum a b c = cyclicNumerator a b c / ((a + b) * (b + c) * (c + a)) := by
  have h1 := ne_of_gt (add_pos ha hb)
  have h2 := ne_of_gt (add_pos hb hc)
  have h3 := ne_of_gt (add_pos hc ha)
  unfold cyclicSum cyclicNumerator
  field_simp

theorem minimum_refinement (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hca : c ≤ a) (hcb : c ≤ b) :
    3 * c ^ 5 * ((a - c) ^ 2 + (b - c) ^ 2) / ((a + b) * (b + c) * (c + a)) ≤
      cyclicSum a b c := by
  rw [denominator_identity a b c ha hb hc]
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr
    (minimum_bound a b c (le_of_lt hc) hca hcb)

theorem positive_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    cyclicSum a b c = 0 ↔ a = b ∧ b = c := by
  constructor
  · intro he
    rw [denominator_identity a b c ha hb hc] at he
    have hz := (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (by positivity))
    exact (numerator_properties a b c ha hb hc).2 hz
  · rintro ⟨rfl, rfl⟩
    unfold cyclicSum
    ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 * b ^ 2 * (b - c) / (a + b) + b ^ 2 * c ^ 2 * (c - a) / (b + c) +
      c ^ 2 * a ^ 2 * (a - b) / (c + a) ≥ 0 := by
  change 0 ≤ cyclicSum a b c
  rw [denominator_identity a b c ha hb hc]
  exact div_nonneg (numerator_properties a b c ha hb hc).1 (by positivity)
