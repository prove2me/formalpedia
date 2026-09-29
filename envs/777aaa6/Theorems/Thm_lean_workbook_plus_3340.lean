-- Prove2me | Theorems.Thm_lean_workbook_plus_3340
-- name    : lean_workbook_plus_3340
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d25f0a83-b183-4fb5-809c-397d52a416de
-- statement:
--   Lemma: If $ p$ is prime, then $ p | ab \implies p | a \text{ or } p | b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3340 (p : ℕ) (hp : p.Prime) (a b : ℕ) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b   :=  by sorry
