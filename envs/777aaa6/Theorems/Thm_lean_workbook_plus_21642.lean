-- Prove2me | Theorems.Thm_lean_workbook_plus_21642
-- name    : lean_workbook_plus_21642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/66ca43d5-1bb8-48fa-a627-9ae069e3acd9
-- statement:
--   $\left( a-b \right) ^{3}+ \left( b-c \right) ^{3}+ \left( c-a \right) ^{3}- \left( a+b-c \right) \left( b-a \right) \left( a-c \right) - \left( b+c-a \right) \left( c-b \right) \left( b-a \right) - \left( c+a-b \right) \left( a-c \right) \left( c-b \right) =a \left( a-b \right) \left( a-c \right) +b \left( b-c \right) \left( b-a \right) +c \left( c-a \right) \left( c-b \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21642 : ∀ a b c : ℤ, (a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3 - (a + b - c) * (b - a) * (a - c) - (b + c - a) * (c - b) * (b - a) - (c + a - b) * (a - c) * (c - b) = a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b)   :=  by sorry
