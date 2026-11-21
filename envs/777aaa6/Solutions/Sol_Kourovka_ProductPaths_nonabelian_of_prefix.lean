-- Prove2me | solution 1 for Kourovka.ProductPaths.nonabelian_of_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:00.222979+00:00
-- url     : https://prove2.me/submissions/ddbbb96d-ad3f-4807-8854-f3e7cff7e7de

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_nonabelian_prefix


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) {u v : List Bool}
    (huv : u <+: v) (hv : Nonabelian f v) : Nonabelian f u := by
  obtain ⟨s, rfl⟩ := huv
  exact nonabelian_prefix f u s hv
end Kourovka.ProductPaths
