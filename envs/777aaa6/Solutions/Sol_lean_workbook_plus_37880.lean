-- Prove2me | solution 1 for lean_workbook_plus_37880
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:05.473576+00:00
-- url     : https://prove2.me/submissions/b6362177-be1c-4493-9549-6b2d3208dc01

import Mathlib.Analysis.Complex.Basic

theorem solution (A: Finset ℕ) (hA: A = Finset.Icc 1 12): ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ i ∈ A, ¬ 3 ∣ (f i - i) := by
  refine ⟨fun i => i + 1, fun x y h => by simpa using h, ?_⟩
  intro i _
  show ¬ 3 ∣ (i + 1 - i)
  omega
