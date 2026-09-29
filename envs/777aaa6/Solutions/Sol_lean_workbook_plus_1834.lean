-- Prove2me | solution 1 for lean_workbook_plus_1834
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:53.573432+00:00
-- url     : https://prove2.me/submissions/06af9dab-57ff-4ba6-a951-b35723d74e29

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 4^(37) + 4^(1000) + 4^(1962) = (2^(1962) + 2^(37))^2 := by
  intros
  grind
