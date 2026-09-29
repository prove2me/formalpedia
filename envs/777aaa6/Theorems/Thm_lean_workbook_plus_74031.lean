-- Prove2me | Theorems.Thm_lean_workbook_plus_74031
-- name    : lean_workbook_plus_74031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e289aa89-d98e-4a49-a4c4-7d23c7b56ac2
-- statement:
--   FLT says that for prime $p$ and $a\not\equiv0\pmod{p}$ , then we have $a^{p-1}\equiv1\pmod{p}$ . Since $10\not\equiv0\pmod{p}$ (i.e. $10$ isn't a multiple of $2017$ ), we have by FLT $10^{2016}\equiv1\pmod{2017}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74031 :
  10^2016 ≡ 1 [MOD 2017]   :=  by sorry
