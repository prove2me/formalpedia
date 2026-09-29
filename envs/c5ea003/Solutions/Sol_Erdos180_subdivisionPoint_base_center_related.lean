-- Prove2me | solution 1 for Erdos180.subdivisionPoint_base_center_related
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:44:16.131359+00:00
-- url     : https://prove2.me/submissions/4d96c56f-aaaf-4de5-aabf-d3980a0c90fb

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorems.Thm_Erdos180_subdivisionPoint_pair_incidence

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    SymplecticPointRelated K p c := by
  obtain ⟨L, _, hpL, hcL⟩ :=
    subdivisionPoint_pair_incidence K copy hbase hcenter
  refine ⟨?_, L, hpL, hcL⟩
  intro hpc
  have hvertex :
      (Sum.inl (Sum.inl base) : SubdivisionVertex k) =
        .inl (.inr center) := by
    apply copy.injective
    change copy (.inl (.inl base)) =
      copy (.inl (.inr center))
    rw [hbase, hcenter, hpc]
  cases hvertex
