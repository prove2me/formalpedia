-- Prove2me | Theorems.Thm_WorkbookRestored_plus_51564
-- name    : WorkbookRestored.plus_51564
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:39:50.911966+00:00
-- url     : https://prove2.me/theorems/45b0de19-bdfc-49b9-88b2-02a9ecc4b120
-- title:
--   Choosing zero elements
-- statement:
--   For every natural number $n$, $\binom n0=1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_51564` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/eed219fd-9fe2-4c1d-bdc9-5bbdeda0f160); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_51564; immutable original Prove2Me node eed219fd-9fe2-4c1d-bdc9-5bbdeda0f160

import Mathlib.Data.Nat.Choose.Basic
open Nat

theorem WorkbookRestored.plus_51564 : ∀ n : ℕ, choose n 0 = 1   :=  by sorry
