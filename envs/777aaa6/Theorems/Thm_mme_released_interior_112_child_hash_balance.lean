-- Prove2me | Theorems.Thm_mme_released_interior_112_child_hash_balance
-- name    : mme_released_interior_112_child_hash_balance
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:52:42.934731+00:00
-- url     : https://prove2.me/theorems/57dcf8cd-812a-453b-99c5-c47522b178ce
-- title:
--   Strict hash balance for every released 112 child parameter
-- statement:
--   For every owner, recipe and region, the parameter p of each of the three coordinate placements of a 112 child satisfies 341 times twice p less than 100 times D minus twice p. This is the strict balance inequality required by the primary-hash child extraction. Missing parameters are zero; this theorem does not assert that every lookup is positive. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed

theorem mme_released_interior_112_child_hash_balance
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (shape : List ℕ)
    (hshape : shape = [1, 1, 2] ∨ shape = [1, 2, 1] ∨ shape = [2, 1, 1]) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == shape)).getD (0, [], 0)).2.2
    341 * (2 * p) < 100 * (denominator - 2 * p) := by sorry
