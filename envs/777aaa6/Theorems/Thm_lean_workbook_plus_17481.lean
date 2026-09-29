-- Prove2me | Theorems.Thm_lean_workbook_plus_17481
-- name    : lean_workbook_plus_17481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/37b8db2c-3746-49a6-a72b-3777326269ce
-- statement:
--   Suppose $f: U \rightarrow V, g: V \rightarrow \mathbb{R}$ are continuous functions where $U, V$ are open subsets of $\mathbb{R}$. Prove that the composition $gf: U \rightarrow \mathbb{R}$ is continuous.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17481 (U V : Set ℝ) (f : U → V) (g : V → ℝ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f)   :=  by sorry
