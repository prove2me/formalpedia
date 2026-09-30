-- Prove2me | solution 1 for lean_workbook_plus_17305
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:00:19.835576+00:00
-- url     : https://prove2.me/submissions/1ed9a31c-aab6-48fe-be75-2aff4a5608f4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ReciprocalConstraintCyclic

theorem reciprocal_sum (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a + 1 / b + 1 / c = (a * b + a * c + b * c) / (a * b * c) := by
  field_simp
  ring

theorem constraint_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a + 1 / b + 1 / c ≤ 1 ↔ 0 ≤ a * b * c - a * b - a * c - b * c := by
  rw [reciprocal_sum a b c ha hb hc, div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

theorem pair_domain (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 0 ≤ a * b * c - a * b - a * c - b * c) :
    0 < b * c - b - c ∧ 4 < b + c ∧ 0 < a + b + c - 1 := by
  have hbc : 0 < b * c := mul_pos hb hc
  have hmul : b * c ≤ a * (b * c - b - c) := by nlinarith
  have hv : 0 < b * c - b - c := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
    linarith
  have hu : 4 < b + c := by
    have hs := sq_nonneg (b - c)
    by_contra hn
    have := mul_nonneg (show 0 ≤ b + c by positivity) (show 0 ≤ 4 - (b + c) by linarith)
    nlinarith
  exact ⟨hv, hu, by linarith⟩

theorem gap_identity (a b c : ℝ) :
    ((a + b + c - 1) * (b + c) - 4 * (a + b * c)) * (b * c - b - c) =
      (b + c - 4) * (a * b * c - a * b - a * c - b * c) +
        (b - c) ^ 2 * (b * c - b - c + 1) := by ring

theorem polynomial_gap (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 0 ≤ a * b * c - a * b - a * c - b * c) :
    0 ≤ (a + b + c - 1) * (b + c) - 4 * (a + b * c) := by
  obtain ⟨hv, hu, _⟩ := pair_domain a b c ha hb hc h
  have hfirst := mul_nonneg (show 0 ≤ b + c - 4 by linarith) h
  have hsecond := mul_nonneg (sq_nonneg (b - c))
    (show 0 ≤ b * c - b - c + 1 by linarith)
  have hid := gap_identity a b c
  exact nonneg_of_mul_nonneg_left (by linarith) hv

theorem polynomial_gap_eq_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 0 ≤ a * b * c - a * b - a * c - b * c) :
    (a + b + c - 1) * (b + c) - 4 * (a + b * c) = 0 ↔
      b = c ∧ a * b * c - a * b - a * c - b * c = 0 := by
  obtain ⟨hv, hu, _⟩ := pair_domain a b c ha hb hc h
  have hfirst := mul_nonneg (show 0 ≤ b + c - 4 by linarith) h
  have hsecond := mul_nonneg (sq_nonneg (b - c))
    (show 0 ≤ b * c - b - c + 1 by linarith)
  have hid := gap_identity a b c
  constructor
  · intro heq
    have he1 : (b + c - 4) * (a * b * c - a * b - a * c - b * c) = 0 := by
      rw [heq, zero_mul] at hid
      linarith
    have he2 : (b - c) ^ 2 * (b * c - b - c + 1) = 0 := by
      rw [heq, zero_mul] at hid
      linarith
    have hh := (mul_eq_zero.mp he1).resolve_left (ne_of_gt (by linarith : 0 < b + c - 4))
    have hs := (mul_eq_zero.mp he2).resolve_right
      (ne_of_gt (by linarith : 0 < b * c - b - c + 1))
    exact ⟨by nlinarith [sq_nonneg (b - c)], hh⟩
  · rintro ⟨rfl, hh⟩
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, hh, mul_zero, add_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_right hv.ne'

theorem term_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≤ 1) :
    4 / (a + b + c - 1) ≤ (b + c) / (a + b * c) := by
  have hp := (constraint_iff a b c ha hb hc).mp h
  have hd := (pair_domain a b c ha hb hc hp).2.2
  apply (div_le_div_iff₀ hd (by positivity)).mpr
  nlinarith [polynomial_gap a b c ha hb hc hp]

theorem term_eq_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≤ 1) :
    (b + c) / (a + b * c) = 4 / (a + b + c - 1) ↔
      b = c ∧ 1 / a + 1 / b + 1 / c = 1 := by
  have hp := (constraint_iff a b c ha hb hc).mp h
  have hd := (pair_domain a b c ha hb hc hp).2.2
  have hden : 0 < a + b * c := by positivity
  rw [div_eq_div_iff hden.ne' hd.ne']
  have he := polynomial_gap_eq_iff a b c ha hb hc hp
  rw [reciprocal_sum a b c ha hb hc, div_eq_one_iff_eq (by positivity : a * b * c ≠ 0)]
  constructor
  · intro hh
    obtain ⟨hbc, hp0⟩ := he.mp (by nlinarith)
    exact ⟨hbc, by nlinarith⟩
  · rintro ⟨hbc, hh⟩
    have := he.mpr ⟨hbc, by nlinarith⟩
    nlinarith

theorem source_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≤ 1) :
    12 / (a + b + c - 1) ≤
      (b + c) / (a + b * c) + (a + c) / (b + a * c) + (b + a) / (c + a * b) := by
  have h1 := term_bound a b c ha hb hc h
  have h2 := term_bound b a c hb ha hc (by linarith)
  have h3 := term_bound c b a hc hb ha (by linarith)
  convert add_le_add (add_le_add h1 h2) h3 using 1 <;> ring

theorem source_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c ≤ 1) :
    (b + c) / (a + b * c) + (a + c) / (b + a * c) + (b + a) / (c + a * b) =
      12 / (a + b + c - 1) ↔ a = 3 ∧ b = 3 ∧ c = 3 := by
  constructor
  · intro heq
    have h1 := term_bound a b c ha hb hc h
    have h2 := term_bound b a c hb ha hc (by linarith)
    have h3 := term_bound c b a hc hb ha (by linarith)
    have hp2 : b + a + c - 1 = a + b + c - 1 := by ring
    have hp3 : c + b + a - 1 = a + b + c - 1 := by ring
    rw [hp2] at h2
    rw [hp3, mul_comm b a] at h3
    have heq' : 12 / (a + b + c - 1) = 3 * (4 / (a + b + c - 1)) := by ring
    rw [heq'] at heq
    have he1 : (b + c) / (a + b * c) = 4 / (a + b + c - 1) := by linarith
    have he2 : (a + c) / (b + a * c) = 4 / (b + a + c - 1) := by rw [hp2]; linarith
    obtain ⟨hbc, hs⟩ := (term_eq_iff a b c ha hb hc h).mp he1
    obtain ⟨hac, _⟩ := (term_eq_iff b a c hb ha hc (by linarith)).mp he2
    subst a
    subst b
    have hc0 := hc.ne'
    field_simp at hs
    have hc3 : c = 3 := by nlinarith
    exact ⟨hc3, hc3, hc3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem sharp_coefficient (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → 1 / a + 1 / b + 1 / c ≤ 1 →
      k / (a + b + c - 1) ≤
        (b + c) / (a + b * c) + (a + c) / (b + a * c) + (b + a) / (c + a * b)) ↔
      k ≤ 12 := by
  constructor
  · intro h
    have := h 3 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    have ht : k ≤ (3 / 2 : ℝ) * 8 := (div_le_iff₀ (by norm_num)).mp this
    norm_num at ht
    exact ht
  · intro hk a b c ha hb hc h
    have hp := (constraint_iff a b c ha hb hc).mp h
    exact (div_le_div_of_nonneg_right hk (pair_domain a b c ha hb hc hp).2.2.le).trans
      (source_bound a b c ha hb hc h)

end ReciprocalConstraintCyclic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_habc : a * b * c = 1) (h : 1 / a + 1 / b + 1 / c ≤ 1) :
    (b + c) / (a + b * c) + (a + c) / (b + a * c) + (b + a) / (c + a * b) ≥
      12 / (a + b + c - 1) := by
  exact ReciprocalConstraintCyclic.source_bound a b c ha hb hc h

#print axioms ReciprocalConstraintCyclic.reciprocal_sum
#print axioms ReciprocalConstraintCyclic.constraint_iff
#print axioms ReciprocalConstraintCyclic.pair_domain
#print axioms ReciprocalConstraintCyclic.gap_identity
#print axioms ReciprocalConstraintCyclic.polynomial_gap
#print axioms ReciprocalConstraintCyclic.polynomial_gap_eq_iff
#print axioms ReciprocalConstraintCyclic.term_bound
#print axioms ReciprocalConstraintCyclic.term_eq_iff
#print axioms ReciprocalConstraintCyclic.source_bound
#print axioms ReciprocalConstraintCyclic.source_equality
#print axioms ReciprocalConstraintCyclic.sharp_coefficient
#print axioms solution
