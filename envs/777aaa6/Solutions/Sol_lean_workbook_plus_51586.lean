-- Prove2me | solution 1 for lean_workbook_plus_51586
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:43.383388+00:00
-- url     : https://prove2.me/submissions/6cd63356-b537-4733-ae0b-12d42c037492

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (n : ℕ) (i : ℕ) (hi : i ≤ (n-1)/2) :
    (n*i + 2*i + 1) % (n+1) = (i + 1) % (n+1) := by
  have h : n*i + 2*i + 1 = (n+1)*i + (i+1) := by ring
  rw [h]
  simp [Nat.add_mod]
