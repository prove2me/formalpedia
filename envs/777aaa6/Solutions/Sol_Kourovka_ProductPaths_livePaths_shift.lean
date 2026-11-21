-- Prove2me | solution 1 for Kourovka.ProductPaths.livePaths_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:22.166929+00:00
-- url     : https://prove2.me/submissions/cc5f3af3-09b4-4f15-ad2c-c8c12cca6955

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
import Theorems.Thm_Kourovka_ProductPaths_initialWord_succ
import Theorems.Thm_Kourovka_ProductPaths_nonabelian_suffix


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (x : ℕ → Bool) (hx : x ∈ livePaths f) :
    FinitePaths.shift x ∈ livePaths f := by
  intro n
  have h := hx (n + 1)
  rw [initialWord_succ] at h
  exact nonabelian_suffix f [x 0] (initialWord n (FinitePaths.shift x)) h
end Kourovka.ProductPaths
