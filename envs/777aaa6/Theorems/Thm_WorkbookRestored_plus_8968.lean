-- Prove2me | Theorems.Thm_WorkbookRestored_plus_8968
-- name    : WorkbookRestored.plus_8968
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:32.11912+00:00
-- url     : https://prove2.me/theorems/4823a175-eaef-412b-8f39-e330e4d3e017
-- title:
--   A numerical diagonal sum in Pascal’s triangle
-- statement:
--   The binomial coefficients satisfy $$\binom30+\binom41+\binom52=\binom62.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/aff26194-f2bc-4d1c-980c-fca599f3bcc2), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_8968` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_8968; original Prove2Me node aff26194-f2bc-4d1c-980c-fca599f3bcc2; Apache-2.0

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_8968 : choose 3 0 + choose 4 1 + choose 5 2 = choose 6 2   :=  by sorry
