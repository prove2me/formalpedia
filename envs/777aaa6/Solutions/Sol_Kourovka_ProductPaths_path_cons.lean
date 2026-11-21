-- Prove2me | solution 1 for Kourovka.ProductPaths.path_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:15.674098+00:00
-- url     : https://prove2.me/submissions/c90a157a-ad62-4766-a46c-30cf8d3ff329

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (i : Bool) (is : List Bool) (x : A × B) :
    path f (i :: is) x = axis i (f (path f is x)) := rfl
end Kourovka.ProductPaths
