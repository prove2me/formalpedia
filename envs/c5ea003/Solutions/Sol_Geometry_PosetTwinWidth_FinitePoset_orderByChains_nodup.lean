-- Prove2me | solution 1 for Geometry.PosetTwinWidth.FinitePoset.orderByChains_nodup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:22:49.386905+00:00
-- url     : https://prove2.me/submissions/12561635-9e91-4054-9512-c969a3379a30

import Mathlib
import Definitions.Def_Geometry_Contractions
import Definitions.Def_Geometry_PosetTheory_NonCircular
import Definitions.Def_Geometry_PosetTwinWidth_LinearBound
open Geometry.PosetTwinWidth in
theorem solution (P : FinitePoset) {k : ℕ} (C : P.ChainCover k) : (P.orderByChains C).Nodup := by
  unfold FinitePoset.orderByChains
  rw [List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · -- each chain is listed without repetition
    intro l hl
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
    exact Finset.nodup_toList _
  · -- different chains have different indices, hence no common element
    rw [List.pairwise_map]
    refine (List.nodup_finRange k).imp fun {i j} hij => ?_
    rw [List.disjoint_left]
    intro v hvi hvj
    simp only [FinitePoset.chainList, Combinatorics.NonCircular.order, Finset.mem_toList,
      Finset.mem_filter] at hvi hvj
    exact hij (hvi.2.symm.trans hvj.2)
