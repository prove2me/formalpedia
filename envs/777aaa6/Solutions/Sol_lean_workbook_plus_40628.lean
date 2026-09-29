-- Prove2me | solution 1 for lean_workbook_plus_40628
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:48.98229+00:00
-- url     : https://prove2.me/submissions/cd37c79b-7639-4f63-bea1-8fbacd42de2e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (X : Type*) [Countable X] (A : Set X) : Countable A := by
  intros
  exact?
