-- Prove2me | Theorems.Thm_lean_workbook_plus_60536
-- name    : lean_workbook_plus_60536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/4cbfa563-ec8d-443a-99f3-9de595a0b865
-- statement:
--   Explain the step $1200x \pmod {1199} \equiv x \pmod {1199}$ given $1200 \equiv 1 \pmod {1199}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60536 (x : ℕ) : 1200 * x ≡ x [ZMOD 1199]   :=  by sorry
