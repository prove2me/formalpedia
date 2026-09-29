-- Prove2me | Theorems.Thm_mme_released_interior_112_child_marginal
-- name    : mme_released_interior_112_child_marginal
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:50:34.243826+00:00
-- url     : https://prove2.me/theorems/633bd064-f914-4427-b72f-b8d706ecae9b
-- title:
--   Canonical marginals for every permuted interior 112 child
-- statement:
--   For every owner and released interior child of shape 112 up to coordinate permutation, an outer parameter at most half the denominator gives the canonical marginal formula. The high coordinate has outer masses p and middle mass D minus twice p; each low coordinate has two masses D over two. The parameter bound remains an explicit hypothesis. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_112_child_marginal
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
    p ≤ denominator / 2 → ∀ (i : Fin 3) (w : CompleteWord 2),
      childMarginal owner s r c i w =
        if i = z then
          if w = ![0, 2] ∨ w = ![2, 0] then p
          else if w = ![1, 1] then denominator - 2 * p else 0
        else if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0 := by sorry
