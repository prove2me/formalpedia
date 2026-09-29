-- Prove2me | Theorems.Thm_lean_workbook_plus_44182
-- name    : lean_workbook_plus_44182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/59ecbb5b-ca1a-480d-a2c9-97a1f0c93856
-- statement:
--   Thus $a+1\equiv 0\pmod p\Longleftrightarrow p\mid a+1$ $\blacksquare$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44182 (p a : ℕ) : a + 1 ≡ 0 [ZMOD p] ↔ p ∣ a + 1   :=  by sorry
