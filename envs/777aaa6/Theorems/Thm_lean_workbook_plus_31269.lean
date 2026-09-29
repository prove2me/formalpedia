-- Prove2me | Theorems.Thm_lean_workbook_plus_31269
-- name    : lean_workbook_plus_31269
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/33994612-8887-4b13-92c9-fb09fbb81911
-- statement:
--   Prove that each element $a$ in the set ${1, 2, 3, 4, 5, 6...p-2, p-1}$ has an inverse $b$ in the same set modulo $p$, where $p$ is a prime number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31269 (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) : ∃ b : ZMod p, a * b = 1   :=  by sorry
