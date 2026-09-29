-- Prove2me | Theorems.Thm_lean_workbook_plus_46372
-- name    : lean_workbook_plus_46372
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/161e9891-615a-4918-b37c-f43914847dbe
-- statement:
--   For any two numbers $x,y$ that satisfy $x+y\leq5$ and range from $1$ to $4$ , there are $10$ ordered pairs $(x,y)$ that work, $(1,1),(1,2),(2,1),(1,3),(2,2),(3,1),(1,4),(2,3),(3,2),(4,1).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46372 ∀ x y, x+y<=5 ∧ 1<=x ∧ x<=4 ∧ 1<=y ∧ y<=4 → (x,y)=(1,1)∨(x,y)=(1,2)∨(x,y)=(2,1)∨(x,y)=(1,3)∨(x,y)=(2,2)∨(x,y)=(3,1)∨(x,y)=(1,4)∨(x,y)=(2,3)∨(x,y)=(3,2)∨(x,y)=(4,1)   :=  by sorry
