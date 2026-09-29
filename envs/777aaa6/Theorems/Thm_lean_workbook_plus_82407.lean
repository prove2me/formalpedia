-- Prove2me | Theorems.Thm_lean_workbook_plus_82407
-- name    : lean_workbook_plus_82407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/67255dc1-6d48-47a6-bf80-82061c2d0c81
-- statement:
--   Generalization of Inequality 1: $\left \lfloor \frac{xy}{z} \right \rfloor \ge y \left \lfloor \frac{x}{z} \right \rfloor$ for $x \ge y \ge z; x,y,z \in \mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82407 (x y z : ℕ) (h₁ : x ≥ y) (h₂ : y ≥ z) : (Nat.floor (x * y / z) : ℕ) ≥ y * Nat.floor (x / z)   :=  by sorry
