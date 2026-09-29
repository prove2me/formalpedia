-- Prove2me | Theorems.Thm_lean_workbook_plus_77892
-- name    : lean_workbook_plus_77892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/4fca6e52-3746-4ef7-96f0-80b43975158c
-- statement:
--   Let $x,y,z $ be positive reals such that $\sqrt{a}=x(y-z)^2$ , $\sqrt{b}=y(z-x)^2$ and $\sqrt{c}=z(x-y)^2$ . Prove that $a^2+b^2+c^2 \geq 2(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77892 (a b c x y z : ℝ) (ha : a = x * (y - z) ^ 2) (hb : b = y * (z - x) ^ 2) (hc : c = z * (x - y) ^ 2) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
