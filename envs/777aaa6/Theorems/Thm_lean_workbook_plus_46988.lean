-- Prove2me | Theorems.Thm_lean_workbook_plus_46988
-- name    : lean_workbook_plus_46988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c41cf47d-d274-4402-95f5-f65647e50a47
-- statement:
--   Prove that if $n \equiv 2 \mod 3$, then $n^2 + 2 \equiv 0 \mod 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46988 : ∀ n : ℤ, n ≡ 2 [ZMOD 3] → n ^ 2 + 2 ≡ 0 [ZMOD 3]   :=  by sorry
