-- Prove2me | Theorems.Thm_lean_workbook_plus_45884
-- name    : lean_workbook_plus_45884
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d9286d85-ce9f-47a2-974f-4a35928c2cd4
-- statement:
--   If $a,b$ are both odd then $a^2+b^2+c^2 \equiv 2,3 \pmod {4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45884 {a b c : ℤ} (ha : Odd a) (hb : Odd b) : Odd c → a^2 + b^2 + c^2 ≡ 2 [ZMOD 4] ∨ a^2 + b^2 + c^2 ≡ 3 [ZMOD 4]   :=  by sorry
