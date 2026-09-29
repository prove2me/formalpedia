-- Prove2me | solution 1 for NucleusSheafReconstruction.sections_glue_binary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:22:53.19117+00:00
-- url     : https://prove2.me/submissions/bcd08a4c-b5ea-424e-a67c-d54ca161fbf2

import Mathlib
import Definitions.Def_Bridges_NucleusSheafReconstruction
universe u
open NucleusSheafReconstruction in
theorem solution {S : Type u} [CommSemiring S] (U V : Set (NucleusPoint S))
    (hCRT : CongruenceCRT S U V)
    (sU : LocalQuotient S U)
    (sV : LocalQuotient S V)
    (hcompat :
      LocalQuotient.restrict Set.inter_subset_left sU =
      LocalQuotient.restrict Set.inter_subset_right sV) :
    ∃ s : LocalQuotient S (U ∪ V),
      LocalQuotient.restrict Set.subset_union_left s = sU ∧
      LocalQuotient.restrict Set.subset_union_right s = sV := by
  -- pick representatives of the two local sections
  obtain ⟨a, rfl⟩ := RingCon.mk'_surjective (c := sectionCongr S U) sU
  obtain ⟨b, rfl⟩ := RingCon.mk'_surjective (c := sectionCongr S V) sV
  -- compatibility means they agree on every point of `U ∩ V`
  have hab : ∀ x ∈ U ∩ V, x.con a b := by
    have h := hcompat
    change toLocalQuotient (U ∩ V) a = toLocalQuotient (U ∩ V) b at h
    exact (sectionCongr S (U ∩ V)).eq.1 h
  -- the CRT hypothesis glues them to a global representative
  obtain ⟨c, hcU, hcV⟩ := hCRT a b hab
  refine ⟨(sectionCongr S (U ∪ V)).mk' c, ?_, ?_⟩
  · change toLocalQuotient U c = (sectionCongr S U).mk' a
    exact (sectionCongr S U).eq.2 hcU
  · change toLocalQuotient V c = (sectionCongr S V).mk' b
    exact (sectionCongr S V).eq.2 hcV
