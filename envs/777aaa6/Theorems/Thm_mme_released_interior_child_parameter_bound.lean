-- Prove2me | Theorems.Thm_mme_released_interior_child_parameter_bound
-- name    : mme_released_interior_child_parameter_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:15:57.678784+00:00
-- url     : https://prove2.me/theorems/7de0ec63-8763-4341-aa7f-2cc43235d2dc
-- title:
--   Every released child parameter is at most half the denominator
-- statement:
--   A kernel-checked finite certificate bounds every stored child parameter in every released owner and recipe. The public lookup theorem also covers absent parameters, whose default value is zero. This exposes the parameter bound as a standalone dependency for probability normalization and intact tensor certificates. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_child_parameter_bound
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (shape : List ℕ) :
    (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == shape)).getD (0, [], 0)).2.2 ≤
        denominator / 2 := by sorry
