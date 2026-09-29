-- Prove2me | Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
-- name    : mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:38:08.429784+00:00
-- url     : https://prove2.me/theorems/17ad4987-ec1a-4cfc-b77a-9ba715eaf59c
-- title:
--   Exact basis-labelled power descent to $\langle1,1,D\rangle$
-- statement:
--   Let an exact, basis-labelled restriction send a tensor $T$ to $\langle1,1,P\rangle$, with every distinguished $Z$-basis vector sent injectively to its standard matrix-multiplication coordinate. For every power $n$ and every predicate selecting recursive $Z$-basis words, the literal selected-word subtensor of $T^{\otimes n}$ restricts to $\langle1,1,D\rangle$, where $D$ is exactly the number of selected words. The proof must lift the router factorwise, flatten the matrix-multiplication power, normalize its two singleton modes, and preserve the full word coordinate injection.
-- source:
--   Finite tensor-power coordinate projection used for the rectangular component values in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 and Table 2, arXiv:2210.10173v5.

import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_basis_z_allowed_projection

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (n : ℕ)
    (allowed : PowIndex I n → Prop) [DecidablePred allowed]
    {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K 1 1 P).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K 1 1 P).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single (coord i, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)) :
    TensorObj.Restrict
      (MMObj K 1 1 (Nat.card {w : PowIndex I n // allowed w}))
      ((T.kronPow n).basisZAllowedSubtensor
        (kronPowModeBasis T 2 bZ n) allowed) := by
  sorry
