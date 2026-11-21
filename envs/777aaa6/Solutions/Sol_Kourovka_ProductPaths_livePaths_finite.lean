-- Prove2me | solution 1 for Kourovka.ProductPaths.livePaths_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:43:27.917597+00:00
-- url     : https://prove2.me/submissions/1c8091d4-7c99-4753-a2a4-fdce1d861000

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
import Theorems.Thm_Kourovka_ProductPaths_livePaths_prefix_bound
import Theorems.Thm_Kourovka_FinitePaths_finite_of_bounded_prefixes


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) : (livePaths f).Finite :=
  FinitePaths.finite_of_bounded_prefixes (livePaths f) (pathWeight f [])
    (livePaths_prefix_bound f hf)
end Kourovka.ProductPaths
