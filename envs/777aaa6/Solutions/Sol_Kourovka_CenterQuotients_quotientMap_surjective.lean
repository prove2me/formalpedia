-- Prove2me | solution 1 for Kourovka.CenterQuotients.quotientMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:35:27.573725+00:00
-- url     : https://prove2.me/submissions/0d7d076e-e505-4525-a4dc-e8b3bb4eebd0

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_CenterQuotients

set_option autoImplicit true
open Kourovka
open Kourovka.CenterQuotients
variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]
namespace Kourovka.CenterQuotients
theorem _root_.solution (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (quotientMap f hf) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨QuotientGroup.mk x, rfl⟩
end Kourovka.CenterQuotients
