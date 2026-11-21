-- Prove2me | solution 1 for Kourovka.ProductPaths.pathWeight_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:04.52518+00:00
-- url     : https://prove2.me/submissions/0e832cf7-f77b-4e5e-aad4-06c840c0f44e

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr
import Theorems.Thm_Kourovka_CenterWeight_weight_congr
import Theorems.Thm_Kourovka_SolvableWeight_weight_congr


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) :
    pathWeight f [] = CenterWeight.weight (A × B) :=
  (CenterWeight.weight_congr
    (MonoidHom.ofInjective (f := MonoidHom.id (A × B)) Function.injective_id)).symm
end Kourovka.ProductPaths
