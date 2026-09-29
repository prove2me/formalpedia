-- Prove2me | Theorems.Thm_lean_workbook_plus_15038
-- name    : lean_workbook_plus_15038
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3d9b1d72-47a7-4cff-93f8-2bf724c738ce
-- statement:
--   Given $a^c \equiv b^c \pmod {d}$, prove that $a^{2c} \equiv b^{2c} \pmod {d}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15038 {a b c d : ℕ} (h : a^c ≡ b^c [ZMOD d]) : a^(2*c) ≡ b^(2*c) [ZMOD d]   :=  by sorry
