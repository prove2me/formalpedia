-- Prove2me | solution 1 for Kourovka.ProductPaths.axis_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:36.889545+00:00
-- url     : https://prove2.me/submissions/71bf82df-cff8-4ee4-a969-fc52ba898045

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (x : A × B) : axis true x = (1, x.2) := rfl
end Kourovka.ProductPaths
