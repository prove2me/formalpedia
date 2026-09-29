-- Prove2me | Theorems.Thm_lean_workbook_plus_52690
-- name    : lean_workbook_plus_52690
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ca780966-b6a2-45bb-882b-4ab667dae037
-- statement:
--   $ \left\lfloor m^2 + m + \frac {1}{4} \right\rfloor - \left\lfloor m^2 - m + \frac {1}{4} \right\rfloor = 2m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52690 : ∀ m : ℤ, (Int.floor (m^2 + m + 1 / 4) - Int.floor (m^2 - m + 1 / 4)) = 2 * m   :=  by sorry
