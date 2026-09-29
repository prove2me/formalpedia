-- Prove2me | Theorems.Thm_WorkbookRestored_plus_38834
-- name    : WorkbookRestored.plus_38834
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:35:19.136777+00:00
-- url     : https://prove2.me/theorems/05bcef1e-a0a5-426a-a13c-4d8b760d7f22
-- title:
--   Lean-Workbook Plus 38834: Trigonometric inequality
-- statement:
--   **Lean-Workbook Plus 38834: Middle binomial coefficient bound**
--
--   For natural numbers $n,k$ with $k\le n$, $\binom nk\le\binom n{\lfloor n/2\rfloor}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_38834` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/9f0dbaeb-47c5-4ed2-92d2-369afa7f9981); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_38834; immutable original Prove2Me node 9f0dbaeb-47c5-4ed2-92d2-369afa7f9981

import Mathlib.Data.Nat.Choose.Bounds
open Nat

theorem WorkbookRestored.plus_38834 (n k : ℕ) (h₀ : k ≤ n) : choose n k ≤ choose n (n/2)   :=  by sorry
