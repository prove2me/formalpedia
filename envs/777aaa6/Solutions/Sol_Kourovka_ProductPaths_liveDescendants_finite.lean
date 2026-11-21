-- Prove2me | solution 1 for Kourovka.ProductPaths.liveDescendants_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:06.369148+00:00
-- url     : https://prove2.me/submissions/1007d52f-7b67-4a6b-94b7-99aef807fc62

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (n : ℕ) :
    ∀ w, (liveDescendants f w n).Finite := by
  induction n with
  | zero =>
      intro w
      exact (Set.finite_singleton w).subset (fun _ h => h.1)
  | succ n ih =>
      intro w
      exact (ih (w ++ [false])).union (ih (w ++ [true]))
end Kourovka.ProductPaths
