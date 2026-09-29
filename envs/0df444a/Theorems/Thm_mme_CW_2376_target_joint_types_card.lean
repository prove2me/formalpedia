-- Prove2me | Theorems.Thm_mme_CW_2376_target_joint_types_card
-- name    : mme_CW_2376_target_joint_types_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:18:07.476322+00:00
-- url     : https://prove2.me/theorems/219e2094-8ca4-4993-ab81-452a03175bc1
-- title:
--   The squared CW five-grading has fifteen supported joint types
-- statement:
--   The supported joint types used by the optimized squared Coppersmith--Winograd five-grading form a set of cardinality fifteen. Equivalently, the finite subtype of supported grade triples has fifteen elements.
--
--   This exact cardinality supplies the exponent in the bound that the family of supported joint multiplicity tables with entries at most $N$ has size at most $(N+1)^{15}$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the fifteen five-grading constituents on journal pp. 265--268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_dominance_weights

open MME

theorem mme_CW_2376_target_joint_types_card :
    cw2376TargetJointTypes.card = 15 ∧
      Fintype.card {sigma : Fin 3 → Fin 5 //
        sigma ∈ cw2376TargetJointTypes} = 15 := by
  sorry
