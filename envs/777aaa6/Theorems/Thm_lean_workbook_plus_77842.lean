-- Prove2me | Theorems.Thm_lean_workbook_plus_77842
-- name    : lean_workbook_plus_77842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5e46dd0b-d9ad-47e9-91ca-e2ff79b97285
-- statement:
--   Prove that if $ a \equiv b (\text{mod} \text{m})$ and $b \equiv c (\text{mod} \text{m})$ , then $a \equiv c (\text{mod} \text{m})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77842 {a b c m : ℤ} (hab : a ≡ b [ZMOD m]) (hbc : b ≡ c [ZMOD m]) : a ≡ c [ZMOD m]   :=  by sorry
