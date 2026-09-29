-- Prove2me | solution 1 for Heisenberg125.Heis.asum_of_const
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:41:56.703524+00:00
-- url     : https://prove2.me/submissions/b2db3599-f0ff-4c0b-a9d8-b89ed786d3ae

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_CosetBound
import Definitions.Def_Algebra_Heisenberg125_LowerBound
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} {L : List (Heis p)} {α : ZMod p} (h : ∀ g ∈ L, g.a = α) :
    asum L = α * (L.length : ℕ) := by
  -- every first coordinate is `α`
  have hmap : L.map Heis.a = List.replicate L.length α := by
    rw [List.eq_replicate_iff]
    refine ⟨List.length_map _, fun b hb => ?_⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact h g hg
  unfold asum
  rw [hmap, List.sum_replicate, nsmul_eq_mul, mul_comm]
