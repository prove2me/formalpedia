-- Prove2me | Theorems.Thm_Kourovka_CenterWeight_split
-- name    : Kourovka.CenterWeight.split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:37.11526+00:00
-- url     : https://prove2.me/theorems/57f74dec-9abc-4ffa-8768-933f53fa5f3f
-- title:
--   Center Weight: split
-- statement:
--   A commuting product splits its branching budget among its factors.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L45-L51
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L45-L51

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight
set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]

theorem Kourovka.CenterWeight.split (P Q : Subgroup G) [Group.FG P] [Group.FG Q]
    (hc : ∀ p : P, ∀ q : Q, Commute (p : G) (q : G))
    (hcover : ∀ g : G, ∃ p : P, ∃ q : Q, (p : G) * q = g) :
    weight P + weight Q ≤ weight G := by sorry
