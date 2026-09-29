-- Prove2me | Theorems.Thm_lean_workbook_plus_20954
-- name    : lean_workbook_plus_20954
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/41316302-a730-4c30-91f0-d5d8936cddfb
-- statement:
--   Given bijections $f:B\rightarrow C$ and $g:A\rightarrow B$, prove that $f\circ g:A\rightarrow C$ is also a bijection.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20954 (A B C: Type) (f : B → C) (g : A → B) (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (f ∘ g)   :=  by sorry
