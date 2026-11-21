-- Prove2me | solution 1 for Kourovka.ProductPaths.axis_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:30:23.207205+00:00
-- url     : https://prove2.me/submissions/1770877f-c056-428c-8536-21664ae9b3b2

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
theorem _root_.solution (x : A × B) : axis false x * axis true x = x := by
  ext <;> simp
end Kourovka.ProductPaths
