-- Prove2me | solution 1 for Kourovka.CenterWeight.split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:55.283111+00:00
-- url     : https://prove2.me/submissions/2d187336-c057-41f6-95ed-d83fb4645cc1

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight
import Theorems.Thm_Kourovka_CenterWeight_weight_congr
import Theorems.Thm_Kourovka_AbelianWeight_weight_add_le
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr
import Theorems.Thm_Kourovka_SolvableWeight_weight_add_le
import Theorems.Thm_Kourovka_SolvableWeight_weight_congr


set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]
namespace Kourovka.CenterWeight
theorem _root_.solution (P Q : Subgroup G) [Group.FG P] [Group.FG Q]
    (hc : ∀ p : P, ∀ q : Q, Commute (p : G) (q : G))
    (hcover : ∀ g : G, ∃ p : P, ∃ q : Q, (p : G) * q = g) :
    weight P + weight Q ≤ weight G := by
  have h := SolvableWeight.weight_add_le (P ⧸ Subgroup.center P) (Q ⧸ Subgroup.center Q)
  rw [SolvableWeight.weight_congr _ _ (CentralProducts.quotientEquiv P Q hc hcover)] at h
  exact h
end Kourovka.CenterWeight
