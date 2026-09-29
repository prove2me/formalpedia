-- Prove2me | solution 1 for AATA.correspondence_11_2_4
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:10:12.180317+00:00
-- url     : https://prove2.me/submissions/a1cfef21-22a6-4858-92a9-df27fa4571e5

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

theorem solution {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
    Function.Bijective
      (fun K : {K : Subgroup G // N ≤ K} => K.1.map (QuotientGroup.mk' N)) ∧
    ∀ K : Subgroup G, N ≤ K →
      (K.Normal ↔ (K.map (QuotientGroup.mk' N)).Normal) := by
  constructor
  · exact (QuotientGroup.comapMk'OrderIso N).symm.bijective
  · intro K hNK
    constructor
    · intro hK
      exact hK.map _ (QuotientGroup.mk'_surjective N)
    · intro hK
      have h := hK.comap (QuotientGroup.mk' N)
      simpa only [QuotientGroup.comap_map_mk', sup_of_le_right hNK] using h
