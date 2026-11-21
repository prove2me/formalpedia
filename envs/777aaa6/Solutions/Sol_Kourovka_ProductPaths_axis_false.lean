-- Prove2me | solution 1 for Kourovka.ProductPaths.axis_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:36.482769+00:00
-- url     : https://prove2.me/submissions/635d72d9-58f9-47a6-a185-7e8e852f8f24

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (x : A × B) : axis false x = (x.1, 1) := rfl
end Kourovka.ProductPaths
