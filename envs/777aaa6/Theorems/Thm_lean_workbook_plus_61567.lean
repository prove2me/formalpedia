-- Prove2me | Theorems.Thm_lean_workbook_plus_61567
-- name    : lean_workbook_plus_61567
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b6db176e-9c0c-4a02-bd48-17da93072a30
-- statement:
--   $ ax\equiv1\pmod m$ is just another way of saying that $ ax=1+km$ for some integer $ k.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61567 {a m : ℤ} : a ≡ 1 [ZMOD m] ↔ ∃ k : ℤ, a = 1 + k * m   :=  by sorry
