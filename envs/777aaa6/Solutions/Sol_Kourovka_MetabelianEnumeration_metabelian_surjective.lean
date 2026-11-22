-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.metabelian_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:41:30.672577+00:00
-- url     : https://prove2.me/submissions/836107e9-7b9d-49f5-888a-6e748192dc2c

import Definitions.Def_Kourovka_Computability_Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Definitions.Def_Kourovka_Presentations_Presentations

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : Metabelian G) : Metabelian H := by
  intro a b c d
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, rfl⟩ := hf b
  obtain ⟨c, rfl⟩ := hf c
  obtain ⟨d, rfl⟩ := hf d
  simpa only [map_commutatorElement] using (hG a b c d).map f
end Kourovka.MetabelianEnumeration
