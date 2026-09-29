-- Prove2me | Theorems.Thm_WorkbookSource_plus_78904
-- name    : WorkbookSource.plus_78904
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:11:30.006292+00:00
-- url     : https://prove2.me/theorems/1cd857e2-f742-4226-8dad-f9e1cfb56a64
-- title:
--   A power of two modulo one thousand
-- statement:
--   How to deduce $2^{100} \equiv 376 \pmod {1000}$ from $2^{100} \equiv 1 \pmod {125}$ and $2^{100} \equiv 0 \pmod 8$?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_78904` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_78904; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_78904 : 2 ^ 100 ≡ 1 [ZMOD 125] ∧ 2 ^ 100 ≡ 0 [ZMOD 8] → 2 ^ 100 ≡ 376 [ZMOD 1000]   :=  by sorry
