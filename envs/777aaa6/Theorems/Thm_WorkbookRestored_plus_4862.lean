-- Prove2me | Theorems.Thm_WorkbookRestored_plus_4862
-- name    : WorkbookRestored.plus_4862
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:27.115568+00:00
-- url     : https://prove2.me/theorems/755a0557-276b-4cfb-8bfe-5a4260f6fd69
-- title:
--   Pascal’s binomial identity
-- statement:
--   For natural numbers $n,m$, $$\binom nm+\binom n{m+1}=\binom{n+1}{m+1}.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/ad0d3745-34e0-4cbf-8289-100aa6744fa1), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_4862` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_4862; original Prove2Me node ad0d3745-34e0-4cbf-8289-100aa6744fa1; Apache-2.0

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_4862 (n m : ℕ) : choose n m + choose n (m + 1) = choose (n + 1) (m + 1)   :=  by sorry
