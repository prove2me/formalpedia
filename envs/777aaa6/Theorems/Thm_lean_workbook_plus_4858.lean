-- Prove2me | Theorems.Thm_lean_workbook_plus_4858
-- name    : lean_workbook_plus_4858
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/326d108a-565a-456b-8b8d-463eff0cbe26
-- statement:
--   If $a \equiv b \pmod n$ then $a-b$ is divisible by $n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4858 : ∀ a b n : ℤ, a ≡ b [ZMOD n] → n ∣ (a - b)   :=  by sorry
