-- Prove2me | Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
-- name    : mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:38:10.982579+00:00
-- url     : https://prove2.me/theorems/0097b2bf-c880-4d42-a403-a1e20232018c
-- title:
--   Exact basis-labelled power descent to $\langle D,1,1\rangle$
-- statement:
--   This is the mode-rotated power companion of the $\langle1,1,P\rangle$ descent. An exact, basis-labelled restriction $T\to\langle P,1,1\rangle$ lifts through every Kronecker power and every literal selection of recursive $Z$-basis words, producing $\langle D,1,1\rangle$ with $D$ exactly the selected-word cardinality. No asymptotic estimate or replacement of the selected basis by an abstract space is used.
-- source:
--   Finite tensor-power coordinate projection used for the rectangular component values in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 and Table 2, arXiv:2210.10173v5.

import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_basis_z_allowed_projection

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (n : ℕ)
    (allowed : PowIndex I n → Prop) [DecidablePred allowed]
    {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K P 1 1).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K P 1 1).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single ((0 : Fin 1), coord i) 1 : Fin 1 × Fin P → K)) :
    TensorObj.Restrict
      (MMObj K (Nat.card {w : PowIndex I n // allowed w}) 1 1)
      ((T.kronPow n).basisZAllowedSubtensor
        (kronPowModeBasis T 2 bZ n) allowed) := by
  sorry
