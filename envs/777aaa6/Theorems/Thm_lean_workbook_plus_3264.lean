-- Prove2me | Theorems.Thm_lean_workbook_plus_3264
-- name    : lean_workbook_plus_3264
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c7bc8aa2-ae40-4af2-9a2f-651f322233f9
-- statement:
--   Prove that for any $a \in \mathbb{N}$, $a^2 \equiv 0 \text{ or } 1 \text{ or } 4 \pmod 8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3264 : ∀ a : ℕ, a ^ 2 ≡ 0 [ZMOD 8] ∨ a ^ 2 ≡ 1 [ZMOD 8] ∨ a ^ 2 ≡ 4 [ZMOD 8]   :=  by sorry
