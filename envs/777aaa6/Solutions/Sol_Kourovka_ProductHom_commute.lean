-- Prove2me | solution 1 for Kourovka.ProductHom.commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:30:03.261283+00:00
-- url     : https://prove2.me/submissions/367cc3f9-49f1-4eb3-affe-e02e6f465e63

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
    Commute (left f a) (right f b) := by
  change f (a, 1) * f (1, b) = f (1, b) * f (a, 1)
  rw [← map_mul, ← map_mul]
  simp
end Kourovka.ProductHom
