-- Prove2me | Theorems.Thm_lean_workbook_plus_21675
-- name    : lean_workbook_plus_21675
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9de5824f-c67c-49b6-93a4-0128be9c8998
-- statement:
--   I think the simplest way is to use mods. First of all, note that $ 3^3=27\equiv-1\pmod{28}$ . Hence, $ 3^{114}=(3^3)^{38}\equiv(-1)^{38}\equiv1\pmod{28}$ . Thus, $ 3^{115}=3(3^{114})\equiv3\pmod{28}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21675 :
  (3^115) % 28 = 3   :=  by sorry
