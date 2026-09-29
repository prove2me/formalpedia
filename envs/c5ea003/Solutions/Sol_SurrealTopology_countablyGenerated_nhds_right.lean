-- Prove2me | solution 1 for SurrealTopology.countablyGenerated_nhds_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:14:31.484071+00:00
-- url     : https://prove2.me/submissions/6970f8f9-658d-4d66-bce3-2dc0b587dc34

import Mathlib
import Definitions.Def_Geometry_PosetTheory_SurrealTopology

open Set Filter Topology SurrealTopology in
theorem solution {α : Type*} [LinearOrder α] [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {x : α}
    (hcg : (nhds x).IsCountablyGenerated) :
    HasCountableRightCof x := by
  rintro ⟨b, hb⟩
  obtain ⟨s, hs⟩ := (nhds x).exists_antitone_basis
  choose u hu hsub using fun n => exists_Ico_subset_of_mem_nhds (hs.mem n) ⟨b, hb⟩
  refine ⟨u, hu, fun y hy => ?_⟩
  by_contra hcon
  have hlt : ∀ n, y < u n := fun n => lt_of_not_ge fun h => hcon ⟨n, h⟩
  obtain ⟨n, -, hn⟩ := hs.1.mem_iff.1 (Iio_mem_nhds hy)
  exact lt_irrefl y (hn (hsub n ⟨hy.le, hlt n⟩))
