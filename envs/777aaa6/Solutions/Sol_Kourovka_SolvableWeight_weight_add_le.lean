-- Prove2me | solution 1 for Kourovka.SolvableWeight.weight_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:10.48579+00:00
-- url     : https://prove2.me/submissions/aa92e990-d898-475d-905f-de11eff6eda8

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
import Theorems.Thm_Kourovka_SolvableWeight_weight_congr
import Theorems.Thm_Kourovka_AbelianWeight_weight_add_le
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr


set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]
namespace Kourovka.SolvableWeight
theorem _root_.solution [Group.FG G] [Group.FG H] :
    weight G + weight H ≤ weight (G × H) := by
  have h := AbelianWeight.weight_add_le (Additive (Abelianization G))
    (Additive (Abelianization H))
  have he := AbelianWeight.weight_congr _ _
    ((abelianizationProd G H).toAdditive.trans
      (AddEquiv.prodAdditive (Abelianization G) (Abelianization H)))
  change _ ≤ AbelianWeight.weight (Additive (Abelianization (G × H)))
  rw [he]
  exact h
end Kourovka.SolvableWeight
