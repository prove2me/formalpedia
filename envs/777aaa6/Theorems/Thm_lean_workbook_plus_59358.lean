-- Prove2me | Theorems.Thm_lean_workbook_plus_59358
-- name    : lean_workbook_plus_59358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/4a4d09d2-c607-47ec-a514-d6755de317f4
-- statement:
--   Let $D$ be a compact subset of $\mathbb{R}$ and support that $f: D \rightarrow \mathbb{R}$ is continuous. Prove $f(D)$ is compact.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59358 (D : Set ℝ) (f : ℝ → ℝ)
    (hD : IsCompact D) (hf : ContinuousOn f D) :
    IsCompact (Set.image f D)   :=  by sorry
