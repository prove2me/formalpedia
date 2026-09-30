-- Prove2me | solution 1 for lean_workbook_plus_3200
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:39:13.6973+00:00
-- url     : https://prove2.me/submissions/90651519-ec77-4d5e-b7a3-64d8677c9d14

import Mathlib.Analysis.Complex.Basic

theorem solution (X : Type) [MetricSpace X] (f : X → X) (hf : Continuous f) :
    Continuous (fun x => dist (f x) x) :=
  hf.dist continuous_id

#print axioms solution
