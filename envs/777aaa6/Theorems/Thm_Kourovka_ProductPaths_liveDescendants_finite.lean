-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_liveDescendants_finite
-- name    : Kourovka.ProductPaths.liveDescendants_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:01.291925+00:00
-- url     : https://prove2.me/theorems/1249ad7e-5228-4454-87d9-d5ffabe9cdab
-- title:
--   Product Paths: live Descendants finite
-- statement:
--   The Product Paths construction uses the live Descendants finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L19-L27
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L19-L27

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.liveDescendants_finite (f : A × B →* A × B) (n : ℕ) :
    ∀ w, (liveDescendants f w n).Finite := by sorry
