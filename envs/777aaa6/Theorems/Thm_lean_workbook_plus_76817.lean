-- Prove2me | Theorems.Thm_lean_workbook_plus_76817
-- name    : lean_workbook_plus_76817
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d4f448ba-2afb-4496-8fd5-05006e4a68fc
-- statement:
--   If $f$ and $g$ are uniformly continuous on $R$ , must $f o g$ (composition function $f(g(x))$ ) be uniformly continuous on $R$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76817 (f g : ℝ → ℝ) (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (f ∘ g)   :=  by sorry
