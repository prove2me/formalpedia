-- Prove2me | Theorems.Thm_lean_workbook_plus_46940
-- name    : lean_workbook_plus_46940
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9d1607a1-aa3a-4d05-9dba-1e6b93115f80
-- statement:
--   To find $\gcd(180,594)$, we use the euclidean algorithm. We have \n$594-3\cdot 180=54 \n180-3\cdot 54=18 \n54-3\cdot 18=0$ \nSo $\gcd(180,594)=18$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46940 :
  Nat.gcd 180 594 = 18   :=  by sorry
