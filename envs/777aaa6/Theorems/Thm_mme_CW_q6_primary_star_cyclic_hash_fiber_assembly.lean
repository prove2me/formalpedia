-- Prove2me | Theorems.Thm_mme_CW_q6_primary_star_cyclic_hash_fiber_assembly
-- name    : mme_CW_q6_primary_star_cyclic_hash_fiber_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:50:32.926205+00:00
-- url     : https://prove2.me/theorems/69d44eba-f4f7-4d27-97a6-e88d11a4ee46
-- title:
--   Cyclic assembly of q=6 primary hash stars
-- statement:
--   The cyclic symmetrization of a direct sum of $A$ identical q=6 primary stars restricts to $A^3$ coupled macro blocks. Each macro block is the Kronecker product of $\langle H,H,H\rangle$ with the cyclic high/low survivor. This theorem isolates the exact $A^3$ cyclic label bookkeeping and tensor assembly from both primary-family hashing and Table-2 source routing.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent pp. 270-272; Duan, Wu, and Zhou, arXiv:2210.10173v5, Section 6.3.

import Definitions.Def_coupledQ6OrientedSurvivor
import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_CW_coupled_value

open MME

universe u

set_option autoImplicit false

theorem mme_CW_q6_primary_star_cyclic_hash_fiber_assembly
    {K : Type u} [Field K] (L G A H : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
        TensorObj.kron (MMObj K H H H)
          (coupledQ6Survivor K L G)))
      (cyclicSymmetrization
        (TensorObj.bigAdd (fun _ : Fin A ↦
          TensorObj.kron (MMObj K 1 H 1)
            (coupledQ6OrientedSurvivor K L G)))) := by
  sorry
