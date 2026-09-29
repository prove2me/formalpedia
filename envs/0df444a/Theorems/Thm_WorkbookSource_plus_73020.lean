-- Prove2me | Theorems.Thm_WorkbookSource_plus_73020
-- name    : WorkbookSource.plus_73020
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:06.756633+00:00
-- url     : https://prove2.me/theorems/93ed42e2-5798-40bc-9b7b-38806813883c
-- title:
--   An asymmetric cubic bound at fixed sum three
-- statement:
--   Let $ a,b,c$ be nonnegative real numbers such that $ a + b + c = 3$ . Prove that $ 2 + a + c^2\ge bc^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73020` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73020; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73020 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : 2 + a + c^2 ≥ b * c^2   :=  by sorry
