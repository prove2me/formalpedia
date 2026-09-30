-- Prove2me | solution 1 for lean_workbook_plus_17481
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:39:33.517331+00:00
-- url     : https://prove2.me/submissions/57772c4f-a8d4-4c13-b235-2b83a3c80ba6

import Mathlib.Analysis.Complex.Basic

theorem solution (U V : Set ℝ) (f : U → V) (g : V → ℝ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf

#print axioms solution
