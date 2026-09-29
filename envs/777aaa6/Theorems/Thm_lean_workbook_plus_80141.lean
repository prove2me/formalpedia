-- Prove2me | Theorems.Thm_lean_workbook_plus_80141
-- name    : lean_workbook_plus_80141
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/dff0bbf8-429c-4ec2-975e-400925635d33
-- statement:
--   Surjective means that a function's image is its codomain. In other words, every element of the codomain is mapped to by some element in the domain. For every $y\in Y$ , there is at least one $x\in X$ such that $f(x)=y$ . This is also known as 'onto'.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80141 {X Y : Type*} (f : X → Y) : Function.Surjective f ↔ ∀ y : Y, ∃ x : X, f x = y   :=  by sorry
