-- Prove2me | Theorems.Thm_lean_workbook_plus_32661
-- name    : lean_workbook_plus_32661
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ae4f790f-f5cc-4521-bff7-65f15e59cfb3
-- statement:
--   $13121^k = (95 \times 137 + 106)^k \equiv 106^k \pmod {137}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32661 : ∀ k : ℕ, (13121^k ≡ (95 * 137 + 106)^k [ZMOD 137])   :=  by sorry
