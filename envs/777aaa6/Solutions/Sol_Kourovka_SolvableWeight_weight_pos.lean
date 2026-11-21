-- Prove2me | solution 1 for Kourovka.SolvableWeight.weight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:40.81019+00:00
-- url     : https://prove2.me/submissions/f1880cd8-df91-4165-bc6d-42a90c61129f

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
import Theorems.Thm_Kourovka_SolvableWeight_abelianization_nontrivial
import Theorems.Thm_Kourovka_AbelianWeight_weight_pos


set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]
namespace Kourovka.SolvableWeight
theorem _root_.solution [Group.FG G] [IsSolvable G] [Nontrivial G] : 0 < weight G := by
  letI := abelianization_nontrivial G
  exact AbelianWeight.weight_pos _
end Kourovka.SolvableWeight
