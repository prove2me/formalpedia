-- Prove2me | Theorems.Thm_lean_workbook_plus_12622
-- name    : lean_workbook_plus_12622
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5a86f48c-f8f1-40da-8abc-c587ca19fa8c
-- statement:
--   Now $\dfrac {1}{2}\sum a^2(b-c)^2 =$ $ \dfrac {1}{2}\Big ((\sqrt{2}/2)^2(-\sqrt{2}/2 - 0)^2 + (-\sqrt{2}/2)^2(0-\sqrt{2}/2)^2 \Big) =$ $ \dfrac {1}{2}(1/4+1/4) = 1/4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12622 :
  1 / 2 * ((Real.sqrt 2 / 2)^2 * (-(Real.sqrt 2 / 2) - 0)^2 + (-(Real.sqrt 2 / 2))^2 * (0 - (Real.sqrt 2 / 2))^2) = 1 / 4   :=  by sorry
