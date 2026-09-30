-- Prove2me | solution 1 for lean_workbook_plus_1423
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:37:20.453317+00:00
-- url     : https://prove2.me/submissions/32108e7d-8b01-4978-b0a7-7b7a30e3dda3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem finite_cube_square_deficit_identity {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, (f i - 1) ^ 2 * (f i + 1) =
      (∑ i ∈ s, f i ^ 3) - (∑ i ∈ s, f i ^ 2) - (∑ i ∈ s, f i) + s.card := by
  calc
    _ = ∑ i ∈ s, (f i ^ 3 - f i ^ 2 - f i + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem finite_cube_square_sum_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (h : (∑ i ∈ s, f i ^ 3) ≤ ∑ i ∈ s, f i ^ 2) :
    (∑ i ∈ s, f i) ≤ s.card := by
  have hn : 0 ≤ ∑ i ∈ s, (f i - 1) ^ 2 * (f i + 1) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (by linarith [hf i hi])
  rw [finite_cube_square_deficit_identity] at hn
  linarith

theorem finite_cube_square_sum_equality {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (h : (∑ i ∈ s, f i ^ 3) ≤ ∑ i ∈ s, f i ^ 2) :
    (∑ i ∈ s, f i) = s.card ↔ ∀ i ∈ s, f i = 1 := by
  constructor
  · intro he
    have hn : ∀ i ∈ s, 0 ≤ (f i - 1) ^ 2 * (f i + 1) :=
      fun i hi => mul_nonneg (sq_nonneg _) (by linarith [hf i hi])
    have hs : (∑ i ∈ s, (f i - 1) ^ 2 * (f i + 1)) = 0 := by
      have hnonneg := Finset.sum_nonneg hn
      have hi := finite_cube_square_deficit_identity s f
      linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs
    intro i hi
    have hp : f i + 1 ≠ 0 := ne_of_gt (by linarith [hf i hi])
    have hsq : (f i - 1) ^ 2 = 0 := (mul_eq_zero.mp (hz i hi)).resolve_right hp
    linarith [sq_eq_zero_iff.mp hsq]
  · intro he
    calc
      (∑ i ∈ s, f i) = ∑ _i ∈ s, (1 : ℝ) := Finset.sum_congr rfl he
      _ = s.card := by simp

private theorem triple_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∀ i : Fin 3, 0 ≤ ![a, b, c] i := by
  intro i
  fin_cases i <;> simp [ha, hb, hc]

theorem equal_square_cube_triple_bound (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 ≤ a ^ 2 + b ^ 2 + c ^ 2) :
    a + b + c ≤ 3 := by
  have hf := finite_cube_square_sum_bound Finset.univ (![a, b, c])
    (fun i _hi => triple_nonneg a b c ha hb hc i)
    (by simpa [Fin.sum_univ_succ, add_assoc] using h)
  simpa [Fin.sum_univ_succ, add_assoc] using hf

theorem equal_square_cube_triple_equality (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 ≤ a ^ 2 + b ^ 2 + c ^ 2) :
    a + b + c = 3 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  have hf := finite_cube_square_sum_equality Finset.univ (![a, b, c])
    (fun i _hi => triple_nonneg a b c ha hb hc i)
    (by simpa [Fin.sum_univ_succ, add_assoc] using h)
  simpa [Fin.sum_univ_succ, Fin.forall_fin_succ, add_assoc] using hf

theorem equal_square_cube_triple_attainment :
    (0 : ℝ) < 1 ∧ (1 : ℝ) ^ 2 + 1 ^ 2 + 1 ^ 2 = 1 ^ 3 + 1 ^ 3 + 1 ^ 3 ∧
      (1 : ℝ) + 1 + 1 = 3 := by norm_num

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha2 : a^2 + b^2 + c^2 = a^3 + b^3 + c^3) : a + b + c ≤ 3 :=
  equal_square_cube_triple_bound a b c ha.le hb.le hc.le ha2.ge

#print axioms solution
#print axioms finite_cube_square_deficit_identity
#print axioms finite_cube_square_sum_bound
#print axioms finite_cube_square_sum_equality
#print axioms equal_square_cube_triple_bound
#print axioms equal_square_cube_triple_equality
#print axioms equal_square_cube_triple_attainment
