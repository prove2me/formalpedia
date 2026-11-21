-- Prove2me | solution 1 for Kourovka.ProductPaths.iterateHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:34:35.110709+00:00
-- url     : https://prove2.me/submissions/6ab64668-5045-477f-b3c2-3b18ef74f146

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (n : ℕ) (x : A × B) :
    iterateHom f n x = f^[n] x := rfl
end Kourovka.ProductPaths
