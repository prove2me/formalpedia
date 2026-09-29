-- Prove2me | Theorems.Thm_lean_workbook_plus_73771
-- name    : lean_workbook_plus_73771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4993551f-20a3-433d-988a-d937f3f0af4c
-- statement:
--   Now notice that $ 7 = sqrt{49} < sqrt{50} < sqrt{64}=8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73771 :
  7 < Real.sqrt 50 ∧ Real.sqrt 50 < 8   :=  by sorry
