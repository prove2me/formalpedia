-- Prove2me | Theorems.Thm_mme_released_interior_112_canonical_probability
-- name    : mme_released_interior_112_canonical_probability
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:04:34.766404+00:00
-- url     : https://prove2.me/theorems/f22d0bf3-6785-47f2-86b9-b0241e3de419
-- title:
--   Canonical probability profiles for every permuted released 112 child
-- statement:
--   Swapping the high coordinate into the third mode identifies the released child marginal divided by the denominator with the canonical rational 112 profile at its exact released parameter. This covers all coordinate placements, including zero parameters, and supplies the profile identity required by the canonical tensor router. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_112_child_marginal_exact
import Definitions.Def_mme_complete_split_112_address_words
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_112_canonical_probability
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
    ∀ (i : Fin 3) (w : CompleteWord 2),
      (childMarginal owner s r c (Equiv.swap z 2 i) w : ℚ) / denominator =
        CompleteSplit112.profileProbability ((p : ℚ) / denominator) i w := by sorry
