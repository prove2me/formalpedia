-- Prove2me | Theorems.Thm_WorkbookRestored_plus_795
-- name    : WorkbookRestored.plus_795
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:50:52.778058+00:00
-- url     : https://prove2.me/theorems/5154d1f6-b743-422a-b3b2-d40befe6414d
-- title:
--   Oddness of a one-element binomial coefficient
-- statement:
--   Let $n$ be a nonzero natural number. If $\binom n1$ is odd, then $n$ is odd.
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/51988868-9eea-467e-892f-d8e7e49eae2c), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_795` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_795; original Prove2Me node 51988868-9eea-467e-892f-d8e7e49eae2c; Apache-2.0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_795 (n : ℕ) (h : n ≠ 0) : Odd (choose n 1) → Odd n   :=  by sorry
