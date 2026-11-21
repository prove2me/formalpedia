-- Prove2me | Theorems.Thm_Kourovka_CenterQuotients_retract_trivial_of_killed
-- name    : Kourovka.CenterQuotients.retract_trivial_of_killed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:38.825093+00:00
-- url     : https://prove2.me/theorems/da4d6a97-7eae-425c-8515-2a736d89b4b1
-- title:
--   Center Quotients: retract trivial of killed
-- statement:
--   A soluble retract killed by a surjective endomorphism of a finitely generated group is trivial.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterQuotients.lean#L94-L106
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterQuotients.lean#L94-L106

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_CenterQuotients
set_option autoImplicit true
open Kourovka
open Kourovka.CenterQuotients
variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]

theorem Kourovka.CenterQuotients.retract_trivial_of_killed [Group.FG G] [IsSolvable T]
    (f : G →* G) (hf : Function.Surjective f) (i : T →* G) (r : G →* T)
    (hri : ∀ t, r (i t) = t) (hkill : ∀ t, f (i t) = 1) : ∀ t : T, t = 1 := by sorry
