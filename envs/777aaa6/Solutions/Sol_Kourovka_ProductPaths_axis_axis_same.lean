-- Prove2me | solution 1 for Kourovka.ProductPaths.axis_axis_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:34:34.661677+00:00
-- url     : https://prove2.me/submissions/49f71e41-f86a-43aa-8856-798688b12114

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (i : Bool) (x : A × B) : axis i (axis i x) = axis i x := by
  cases i <;> rfl
end Kourovka.ProductPaths
