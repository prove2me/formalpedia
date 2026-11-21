-- Prove2me | solution 1 for Kourovka.ProductHom.decompose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:50.784439+00:00
-- url     : https://prove2.me/submissions/a90442d1-6621-4f44-a3b7-4deaac67351c

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components

set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
open Kourovka.ProductHom
namespace Kourovka.ProductHom
theorem _root_.solution (f : A × B →* K) (a : A) (b : B) :
    f (a, b) = left f a * right f b := by
  simpa using f.map_mul (a, 1) (1, b)
end Kourovka.ProductHom
