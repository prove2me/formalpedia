-- Prove2me | Theorems.Thm_WorkbookSource_problem_34085
-- name    : WorkbookSource.problem_34085
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:34.44572+00:00
-- url     : https://prove2.me/theorems/fa04e9cd-44fc-4e4a-a8bf-731eeb24d228
-- title:
--   A residue below a Mersenne modulus
-- statement:
--   The integer $2^{16}+1$ has the following residue modulo $2^{31}-1$:
--
--   $$2^{16}+1\equiv65537\pmod{2^{31}-1}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34085` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34085; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34085 : 2^16 + 1 ≡ 65537 [MOD 2^31 - 1]  :=  by sorry
