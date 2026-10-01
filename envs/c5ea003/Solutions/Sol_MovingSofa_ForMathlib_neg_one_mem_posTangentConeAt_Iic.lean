-- Prove2me | solution 1 for MovingSofa.ForMathlib.neg_one_mem_posTangentConeAt_Iic
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:22:51.391931+00:00
-- url     : https://prove2.me/submissions/4e4a754b-db59-490c-a046-08cb291976ec

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a : ℝ) :
    (-1 : ℝ) ∈ posTangentConeAt (Set.Iic a) a :=
  mem_posTangentConeAt_of_segment_subset
    ((convex_Iic a).segment_subset (Set.mem_Iic.2 le_rfl) (Set.mem_Iic.2 (by linarith)))
