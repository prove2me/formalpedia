-- Prove2me | Theorems.Thm_WorkbookSource_problem_43899
-- name    : WorkbookSource.problem_43899
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:42.294075+00:00
-- url     : https://prove2.me/theorems/03e5e213-3134-47a2-bba6-b0b7e5fb3d4e
-- title:
--   Proof by two propositional cases
-- statement:
--   Using logical equivalences, show that $[(p\lor q)\land (p\Rightarrow r)\land (q\Rightarrow r)] \Rightarrow r$
--
--   Source: InternLM Lean-Workbook, record lean_workbook_43899; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43899; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_43899 (p q r : Prop) : ((p ∨ q) ∧ (p → r) ∧ (q → r)) → r  :=  by sorry
