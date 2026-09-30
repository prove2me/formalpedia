-- Prove2me | solution 1 for lean_workbook_plus_67533
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:45.05729+00:00
-- url     : https://prove2.me/submissions/4188e470-2fb2-4b19-a848-9e9aa3486683

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (f : ℕ → ℕ) :
    (∀ m n, f (m + n) = f m + f n) ↔ ∃ a, ∀ n, f n = a * n := by
  constructor
  · intro hf
    have h0 : f 0 = 0 := by
      have h := hf 0 0
      simp only [Nat.add_zero] at h
      omega
    refine ⟨f 1, ?_⟩
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      rw [hf, ih]
      ring
  · rintro ⟨a, ha⟩ m n
    rw [ha (m + n), ha m, ha n]
    ring

#print axioms solution
