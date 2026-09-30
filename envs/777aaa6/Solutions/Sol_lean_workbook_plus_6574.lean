-- Prove2me | solution 1 for lean_workbook_plus_6574
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:53.973112+00:00
-- url     : https://prove2.me/submissions/1c815659-1a2d-4a1c-9a28-d582a5f95d55

import Mathlib.Analysis.Complex.Basic

theorem solution (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ∃ a b, a ≤ (p-1)/2 ∧ b ≤ (p-1)/2 ∧ 1 + a * (p-1) ≡ 1 + b * (p-1) [ZMOD q] :=
  ⟨0, 0, by simp, by simp, Int.ModEq.refl _⟩
