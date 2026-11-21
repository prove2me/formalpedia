-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_crossed_word_not_nonabelian
-- name    : Kourovka.ProductPaths.crossed_word_not_nonabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:57.678165+00:00
-- url     : https://prove2.me/theorems/fae0aaf9-34f4-4950-b339-2c9d20753019
-- title:
--   Product Paths: crossed word not nonabelian
-- statement:
--   The finite-path identity rules out a path with distinct middle and terminal vertices.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/MixedPaths.lean#L13-L30
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/MixedPaths.lean#L13-L30

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_MixedPaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.crossed_word_not_nonabelian (f : A × B →* A × B) (m : ℕ) (hm : 0 < m)
    (hp : ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw)
    (u v : List Bool) (j k : Bool) (hu : u.length = m) (hv : (j :: v).length = m)
    (hjk : j ≠ k) : ¬ Nonabelian f ((u ++ (j :: v)) ++ [k]) := by sorry
