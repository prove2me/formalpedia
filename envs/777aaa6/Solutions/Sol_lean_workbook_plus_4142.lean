-- Prove2me | solution 1 for lean_workbook_plus_4142
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:15.025551+00:00
-- url     : https://prove2.me/submissions/79eb94c7-3380-4e39-aa0e-bf1447443991

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic

theorem solution (E : Type*) [MetricSpace E] (f : E → ℝ)
    (hf : ∀ a : ℝ, IsOpen {x | f x < a} ∧ IsOpen {x | f x > a}) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact (hf a).2.mem_nhds ha
  · intro a ha
    exact (hf a).1.mem_nhds ha

#print axioms solution
