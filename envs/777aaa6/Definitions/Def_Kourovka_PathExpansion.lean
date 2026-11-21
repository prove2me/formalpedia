-- Prove2me | Definitions.Def_Kourovka_PathExpansion
-- name    : Kourovka_PathExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:33:22.826181+00:00
-- url     : https://prove2.me/theorems/5fb10521-9bae-46d4-a83e-ee7da6ec3404
-- title:
--   Path Expansion
-- statement:
--   Definitions and structural lemmas for Path Expansion, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExpansion.lean

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
set_option autoImplicit true
namespace Kourovka
namespace ProductPaths
variable {A B : Type*} [Group A] [Group B]
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allWords n).map (false :: ·) ++ (allWords n).map (true :: ·)
def iterateHom (f : A × B →* A × B) (n : ℕ) : A × B →* A × B :=
  { toFun := f^[n]
    map_one' := iterate_map_one f n
    map_mul' := iterate_map_mul f n }
end ProductPaths
end Kourovka


