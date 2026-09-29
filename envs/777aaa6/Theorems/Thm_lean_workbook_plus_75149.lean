-- Prove2me | Theorems.Thm_lean_workbook_plus_75149
-- name    : lean_workbook_plus_75149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/035d017e-1765-469a-a1a0-f563a672962d
-- statement:
--   Let $z_1, z_2\in\mathbb{C}$ . Then $|z_1+z_2|\le |z_1|+|z_2|$ , with equality for $z_2=kz_1, k\in\mathbb{R}, k\ge0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75149 (z₁ z₂ : ℂ) : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖   :=  by sorry
