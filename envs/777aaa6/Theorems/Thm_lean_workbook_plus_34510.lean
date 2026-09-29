-- Prove2me | Theorems.Thm_lean_workbook_plus_34510
-- name    : lean_workbook_plus_34510
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/794092e1-6426-4619-a73f-34644b306c05
-- statement:
--   It's way simpler as a fact. $(x+y+z)^3=x^3+y^3+z^3+3(x+y)(y+z)(z+x) \ge x^3+y^3+z^3$ Equality holds when two of $x$ , $y$ , $z$ are $0$ . In this case let $x=\sqrt[3]{a^2+2bc}$ , $y=\sqrt[3]{b^2+2ca}$ , $z=\sqrt[3]{c^2+2ab}$ , two of them are zero yields two of $a$ , $b$ , $c$ are zero.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34510 {x y z : ℝ} (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x + y + z) ^ 3 ≥ x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x + y) * (y + z) * (z + x)   :=  by sorry
