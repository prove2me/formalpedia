-- Prove2me | Theorems.Thm_lean_workbook_plus_52252
-- name    : lean_workbook_plus_52252
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/f6e32209-9032-42af-bce9-eb2c615f781b
-- statement:
--   Let $ {\mathbb Q}^ +$ be the set of positive rational numbers. Construct a function $ f : {\mathbb Q}^ + \rightarrow {\mathbb Q}^ +$ such that $ f(xf(y)) = \frac {f(x)}{y}$ for all $ x$ , $ y$ in $ {\mathbb Q}^ +$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52252 : ∃ f : ℚ → ℚ, ∀ x y : ℚ, 0 < x ∧ 0 < y → f (x * f y) = f x / y   :=  by sorry
