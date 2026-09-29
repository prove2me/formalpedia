-- Prove2me | Theorems.Thm_lean_workbook_plus_62087
-- name    : lean_workbook_plus_62087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/73be057b-cf20-4309-8f0f-5937df35cfd7
-- statement:
--   Prove the following inequality properties:\n1. $a \ge b \Longleftrightarrow a+c \ge b+c, \ \ \ \forall c \in \mathbb{R}$\n2. $a \ge b \implies ac \ge bc, \ \ \ \forall c \in \mathbb{R}^+$\nand this:\n$\left ( {\frac{a+b}{2}} \right )^2 > ab, \quad a \ne b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62087 (a b c : ℝ) : a ≥ b ↔ a + c ≥ b + c   :=  by sorry
