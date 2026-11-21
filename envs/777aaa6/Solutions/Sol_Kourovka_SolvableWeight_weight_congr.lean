-- Prove2me | solution 1 for Kourovka.SolvableWeight.weight_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:30:01.945749+00:00
-- url     : https://prove2.me/submissions/28282225-7923-4a27-a7d9-d91f540a2879

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr


set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]
namespace Kourovka.SolvableWeight
theorem _root_.solution (e : G ≃* H) : weight G = weight H :=
  AbelianWeight.weight_congr _ _ e.abelianizationCongr.toAdditive
end Kourovka.SolvableWeight
