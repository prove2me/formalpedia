-- Prove2me | solution 1 for lean_workbook_plus_35917
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:39:23.500206+00:00
-- url     : https://prove2.me/submissions/0e0ba86c-f242-467a-b3d2-b5ce28458e50

import Mathlib.Analysis.Complex.Basic

theorem solution (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => 2 * (f x + g x - |f x - g x|)) :=
  continuous_const.mul ((hf.add hg).sub (hf.sub hg).abs)

#print axioms solution
