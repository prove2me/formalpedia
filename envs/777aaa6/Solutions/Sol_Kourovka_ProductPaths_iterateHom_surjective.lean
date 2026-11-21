-- Prove2me | solution 1 for Kourovka.ProductPaths.iterateHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:34:35.581187+00:00
-- url     : https://prove2.me/submissions/d4fae671-0be8-42e8-8a21-bf82d191abe6

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (iterateHom f n) := hf.iterate n
end Kourovka.ProductPaths
