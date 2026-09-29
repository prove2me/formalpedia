-- Prove2me | Theorems.Thm_WorkbookRestored_plus_52753
-- name    : WorkbookRestored.plus_52753
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:46:04.906356+00:00
-- url     : https://prove2.me/theorems/49939a4b-be86-4988-a274-966fa44df5d8
-- title:
--   Lean-Workbook Plus 52753: Penultimate binomial coefficient
-- statement:
--   For every positive integer $n$, $\binom{n}{n-1}=n$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_52753` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/88d77509-4952-46d0-80b3-2c841d15065e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_52753; immutable original Prove2Me node 88d77509-4952-46d0-80b3-2c841d15065e

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_52753 (n : ℕ) (h : n ≠ 0) : choose n (n-1) = n   :=  by sorry
