-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_primary_hash_family_MM_restrict_of_star_landing
-- name    : mme_dwz_q6_121_211_primary_hash_family_MM_restrict_of_star_landing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:06:10.229207+00:00
-- url     : https://prove2.me/theorems/70d67874-9caa-4617-91ff-8e961d04103b
-- title:
--   Rows 121/211: assemble square MM blocks after exact primary-star landing
-- statement:
--   Assume the literal six-symmetrization of a Table-2 component power already restricts to the cyclic symmetrization of A identical primary stars, each with H arms and the q=6 oriented high/low survivor. Then it restricts to A^3 square matrix-multiplication tensors, each of side H·36^(2G)·6^(2L). This theorem isolates routine cyclic-star, coupled-survivor, Kronecker, and direct-sum assembly from the source-specific row routing.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 5-6; Coppersmith and Winograd, Journal of Symbolic Computation 9 (1990), coupled constituent.

import Definitions.Def_coupledQ6OrientedSurvivor
import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_121_211_primary_hash_family_MM_restrict_of_star_landing
    {K : Type u} [Field K]
    (s : Fin 15) (m L G A H : ℕ)
    (hstars : TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.bigAdd (fun _ : Fin A ↦
          TensorObj.kron (MMObj K 1 H 1)
            (coupledQ6OrientedSurvivor K L G))))
      (sixSymmetrization (restrictedComponentPower K s m))) :
    let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
        MMObj K (H * side) (H * side) (H * side)))
      (sixSymmetrization (restrictedComponentPower K s m)) := by
  sorry
