-- Prove2me | Theorems.Thm_lean_workbook_plus_37160
-- name    : lean_workbook_plus_37160
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e0a3d7ee-0d54-47eb-9e9e-a6953a727bcf
-- statement:
--   Prove that $\binom{2p}{p}\equiv 2 \pmod{p^{3}}$ (without using Wolstenholme of course).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37160 : ∀ p : ℕ, p.Prime → (Nat.choose (2 * p) p) % (p ^ 3) = 2   :=  by sorry
