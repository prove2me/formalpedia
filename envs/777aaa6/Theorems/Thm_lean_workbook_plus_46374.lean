-- Prove2me | Theorems.Thm_lean_workbook_plus_46374
-- name    : lean_workbook_plus_46374
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/78d324bd-8407-4fa6-932f-3e728cca0bc9
-- statement:
--   Fact $a^2 \equiv 0,1$ mod $4 \forall a \in \mathbb Z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46374 : ∀ a : ℤ, a ^ 2 ≡ 0 [ZMOD 4] ∨ a ^ 2 ≡ 1 [ZMOD 4]   :=  by sorry
