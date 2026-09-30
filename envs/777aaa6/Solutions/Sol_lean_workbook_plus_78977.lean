-- Prove2me | solution 1 for lean_workbook_plus_78977
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:13:29.482671+00:00
-- url     : https://prove2.me/submissions/d0d7f4a6-3c9d-4ce2-985f-8b80a0d09db2

import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Mathlib.Tactic

private lemma three_distinct_zero_sum (A : Finset ℕ) (hA : 5 ≤ A.card) :
    ∃ x y z : ℕ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ 3 ∣ x + y + z := by
  obtain ⟨S, hSA, hS, hsum⟩ :=
    Int.erdos_ginzburg_ziv (n := 3) (s := A) (fun x => (x : ℤ)) (by simpa using hA)
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS
  refine ⟨x, y, z, hSA (by simp), hSA (by simp), hSA (by simp), hxy, hxz, hyz, ?_⟩
  have hz : (3 : ℤ) ∣ (x : ℤ) + y + z := by
    simpa [hxy, hxz, hyz, add_assoc] using hsum
  exact_mod_cast hz

theorem solution (A : Finset ℕ) (hA : A.card = 5) :
    ∃ x y z : ℕ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ 3 ∣ x + y + z := by
  obtain ⟨x, y, z, hx, hy, hz, _, _, _, hsum⟩ := three_distinct_zero_sum A hA.ge
  exact ⟨x, y, z, hx, hy, hz, hsum⟩
