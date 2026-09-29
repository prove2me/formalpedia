-- Prove2me | Theorems.Thm_WorkbookRestored_plus_39163
-- name    : WorkbookRestored.plus_39163
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:35:47.480336+00:00
-- url     : https://prove2.me/theorems/271cc60b-31e6-417b-b64b-8a097f75bdbb
-- title:
--   Lean-Workbook Plus 39163: Trigonometric identity
-- statement:
--   **Lean-Workbook Plus 39163: Fibonacci addition identity**
--
--   For natural numbers $n,p$, $F_{n+p+1}=F_{n+1}F_{p+1}+F_nF_p$, where $F_0=0$, $F_1=1$ and $F_{j+2}=F_j+F_{j+1}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_39163` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/097d2c38-c06c-47a8-852c-72c9667b0ecb); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_39163; immutable original Prove2Me node 097d2c38-c06c-47a8-852c-72c9667b0ecb

import Mathlib.Data.Nat.Fib.Basic
open Nat

theorem WorkbookRestored.plus_39163 (n p : ℕ) : fib (n + p + 1) = fib (n + 1) * fib (p + 1) + fib n * fib p   :=  by sorry
