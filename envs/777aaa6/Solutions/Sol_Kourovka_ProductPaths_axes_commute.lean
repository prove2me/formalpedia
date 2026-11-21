-- Prove2me | solution 1 for Kourovka.ProductPaths.axes_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:30:27.017514+00:00
-- url     : https://prove2.me/submissions/af441307-5c51-4d37-863c-cf7945800a7f

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (x y : A × B) : Commute (axis false x) (axis true y) := by
  change (x.1, (1 : B)) * (1, y.2) = (1, y.2) * (x.1, 1)
  simp
end Kourovka.ProductPaths
