-- Prove2me | solution 1 for lean_workbook_plus_9331
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:19.263423+00:00
-- url     : https://prove2.me/submissions/143ce5dd-f953-42f5-9798-a36a35cedf98

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (A : ℝ) : A = 2020 / (1 + 2017 / 2018 + 2017 / 2019) + 2020 / (1 + 2018 / 2017 + 2018 / 2019) + 2020 / (1 + 2019 / 2017 + 2019 / 2018) → A = 2020 := by
  intros
  grind
