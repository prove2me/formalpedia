-- Prove2me | Theorems.Thm_lean_workbook_plus_12719
-- name    : lean_workbook_plus_12719
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f2ce4fbf-10c0-4c74-b5fd-9f883bf7cd43
-- statement:
--   Euhm... $x^{2}+x=y^{2}+y\ \Longleftrightarrow\ \left(x^{2}-y^{2}\right)+\left(x-y\right) = (x-y)(x+y+1) = 0$ ...
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12719 : ∀ x y : ℤ, x^2 + x = y^2 + y ↔ (x - y) * (x + y + 1) = 0   :=  by sorry
