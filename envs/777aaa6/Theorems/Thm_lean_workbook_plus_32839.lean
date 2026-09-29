-- Prove2me | Theorems.Thm_lean_workbook_plus_32839
-- name    : lean_workbook_plus_32839
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c6a1db40-d555-4898-aa17-1032409f597a
-- statement:
--   A function $ f: X\to Y$ is surjective if for each $ y\in Y$ there is at least one $ x\in X$ such that $ f(x) = y$ . A function is injective if for each $ y\in Y$ there is at most one $ x\in X$ such that $ f(x) = y$ . A function is a bijection if it is both injective and surjective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32839 {X Y : Type*} (f : X → Y) : Function.Surjective f ↔ ∀ y, ∃ x, f x = y   :=  by sorry
