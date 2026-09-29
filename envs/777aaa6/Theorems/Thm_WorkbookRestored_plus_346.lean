-- Prove2me | Theorems.Thm_WorkbookRestored_plus_346
-- name    : WorkbookRestored.plus_346
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:02:53.816973+00:00
-- url     : https://prove2.me/theorems/c264f224-3c82-425e-9691-c78bd4d6786b
-- title:
--   Choosing a nested pair of subsets
-- statement:
--   For natural numbers $m\le k\le n$,
--
--   $$\binom nk\binom km=\binom nm\binom{n-m}{k-m}.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_346` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `772ebb0a-ff41-471a-b3be-b37ad0a1b719`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_346; original Prove2Me theorem ID 772ebb0a-ff41-471a-b3be-b37ad0a1b719; Apache-2.0.

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat

theorem WorkbookRestored.plus_346 (n k m : ℕ) (h₁ : k ≤ n) (h₂ : m ≤ k) : choose n k * choose k m = choose n m * choose (n - m) (k - m)   :=  by sorry
