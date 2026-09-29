-- Prove2me | solution 1 for lean_workbook_plus_59850
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:58.012957+00:00
-- url     : https://prove2.me/submissions/7d70f225-9db7-4dfc-a756-104686a109e8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {f : ℕ → ℕ} : (∀ b, ∃ a, f a = b) ↔ Set.range f = Set.univ := by
  intros
  exact Iff.symm Set.eq_univ_iff_forall
