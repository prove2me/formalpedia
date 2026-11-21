-- Prove2me | solution 1 for Kourovka.CenterWeight.weight_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:45.7632+00:00
-- url     : https://prove2.me/submissions/c5acd147-798e-425a-9b2f-11588df95a77

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr
import Theorems.Thm_Kourovka_SolvableWeight_weight_congr


set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]
namespace Kourovka.CenterWeight
theorem _root_.solution (e : G ≃* H) : weight G = weight H :=
  SolvableWeight.weight_congr _ _ (quotientCongr e)
end Kourovka.CenterWeight
