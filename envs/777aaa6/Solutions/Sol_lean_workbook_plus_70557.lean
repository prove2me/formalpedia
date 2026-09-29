-- Prove2me | solution 1 for lean_workbook_plus_70557
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:35.721086+00:00
-- url     : https://prove2.me/submissions/11bf736f-ac22-42d9-a866-48030603e823

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (a b : Fin n → ℕ) : a = b ↔ ∀ i, a i = b i := by
  intros
  aesop (config := {maxRuleApplications := 120})
