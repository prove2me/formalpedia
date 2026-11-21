-- Prove2me | solution 1 for Kourovka.ProductPaths.prefix_extendWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:45.379382+00:00
-- url     : https://prove2.me/submissions/b8bb88d6-4c38-4a43-a42a-11221ea5abb0

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (w : List Bool) :
    w <+: extendWord f w := ⟨_, rfl⟩
end Kourovka.ProductPaths
