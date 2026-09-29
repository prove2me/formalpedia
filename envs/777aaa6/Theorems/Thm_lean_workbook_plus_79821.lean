-- Prove2me | Theorems.Thm_lean_workbook_plus_79821
-- name    : lean_workbook_plus_79821
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/ca837460-cef4-49cc-8aaa-3c301af845e7
-- statement:
--   So we want $2014^{2014^{2014}}\pmod {110}$ . Notice that $\varphi(110)=40$ so Euler's Theorem tells us that $2014^{2014^{2014}}\pmod {110}\equiv 2014^{2014^{2014}\pmod {40}}\pmod {110}$ . Again, $\varphi(40)=16$ so by Euler's Theorem $2014^{2014}\equiv 16\pmod {40}$ . Thus $2014^{2014^{2014}}\equiv 34^{16}\pmod {110}$ . Finally, once notices that $34^3=34\pmod {110}$ so that $34^{16}\equiv 34\cdot 34^5\equiv 34^6\equiv 34^2\equiv \boxed{56}\pmod {110}$ , which is our answer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79821 :
  (2014^((2014^2014) % 40)) % 110 = 56   :=  by sorry
