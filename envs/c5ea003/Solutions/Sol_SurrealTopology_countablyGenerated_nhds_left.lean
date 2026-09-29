-- Prove2me | solution 1 for SurrealTopology.countablyGenerated_nhds_left
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:10:24.178015+00:00
-- url     : https://prove2.me/submissions/4dc1e972-ef07-4a7f-92c8-b24de927b275

import Mathlib
import Definitions.Def_Geometry_PosetTheory_SurrealTopology

open Set Filter Topology SurrealTopology in
theorem solution {α : Type*} [LinearOrder α] [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {x : α}
    (hcg : (nhds x).IsCountablyGenerated) :
    HasCountableLeftCof x := by
  rintro ⟨a, ha⟩
  obtain ⟨s, hs⟩ := (nhds x).exists_antitone_basis
  choose l hl hsub using fun n => exists_Ioc_subset_of_mem_nhds (hs.mem n) ⟨a, ha⟩
  refine ⟨l, hl, fun y hy => ?_⟩
  by_contra hcon
  have hlt : ∀ n, l n < y := fun n => lt_of_not_ge fun h => hcon ⟨n, h⟩
  obtain ⟨n, -, hn⟩ := hs.1.mem_iff.1 (Ioi_mem_nhds hy)
  exact lt_irrefl y (hn (hsub n ⟨hlt n, hy.le⟩))
