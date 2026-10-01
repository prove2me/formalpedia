-- Prove2me | solution 1 for MovingSofa.ForMathlib.one_mem_posTangentConeAt_Ici
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:15:36.668769+00:00
-- url     : https://prove2.me/submissions/a774a3ff-41d9-4e03-a095-bb1b638cdd5e

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a : ℝ) : (1 : ℝ) ∈ posTangentConeAt (Set.Ici a) a :=
  mem_posTangentConeAt_of_segment_subset
    ((convex_Ici a).segment_subset (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith)))
