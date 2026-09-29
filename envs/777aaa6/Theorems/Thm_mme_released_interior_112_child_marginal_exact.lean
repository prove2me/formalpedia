-- Prove2me | Theorems.Thm_mme_released_interior_112_child_marginal_exact
-- name    : mme_released_interior_112_child_marginal_exact
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:54:26.928159+00:00
-- url     : https://prove2.me/theorems/a67b2732-f526-4c9c-a813-e2eca5384d97
-- title:
--   Exact canonical 112 marginals for every released interior recipe
-- statement:
--   Every released child with shape 112 up to coordinate permutation has the canonical marginal formula, without an additional parameter-bound hypothesis. A kernel-checked finite certificate bounds all released child parameters by half the denominator; absent lookups give zero. The high coordinate has masses p, D minus twice p, p, and the low coordinates have two masses D over two. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_112_child_marginal
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_112_child_marginal_exact
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
    ∀ (i : Fin 3) (w : CompleteWord 2),
      childMarginal owner s r c i w =
        if i = z then
          if w = ![0, 2] ∨ w = ![2, 0] then p
          else if w = ![1, 1] then denominator - 2 * p else 0
        else if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0 := by sorry
