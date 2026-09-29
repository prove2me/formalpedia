-- Prove2me | solution 1 for mme_CW_2376_exact_address_block_quotient_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:41:43.61533+00:00
-- url     : https://prove2.me/submissions/d936551d-281d-4c95-9457-e2b0c8b6e4fb

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_rank_bridge

open MME BigOperators

set_option autoImplicit false

universe u

private theorem toQ_kronFin
    {K : Type u} [Field K] {d n : ℕ}
    (f : Fin n → TensorObj K d) :
    TensorQ.toQ (TensorObj.kronFin n f) =
      ∏ i, TensorQ.toQ (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [TensorObj.kronFin, TensorQ.toQ_kron,
        Fin.prod_univ_succ]
      exact congrArg (TensorQ.toQ (f 0) * ·)
        (ih (fun i => f i.succ))

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (a : CW2376ExactProfileAddress m) :
    TensorQ.toQ (cw2376ExactAddressBlock cert a) =
      ∏ σ : Fin 3 → Fin 5,
        (TensorQ.toQ (cert.grading.blockSubtensor σ)) ^
          cw2376ProfileMultiplicity m σ := by
  classical
  rw [cw2376ExactAddressBlock, toQ_kronFin]
  let g : Fin (cw2376ProfileLength m) → (Fin 3 → Fin 5) :=
    fun j => cw2376AddressType a.1 j
  let f : (Fin 3 → Fin 5) → TensorQ K 3 :=
    fun σ => TensorQ.toQ (cert.grading.blockSubtensor σ)
  change (∏ j, f (g j)) = ∏ σ, f σ ^ cw2376ProfileMultiplicity m σ
  rw [← Finset.prod_fiberwise' Finset.univ g f]
  apply Finset.prod_congr rfl
  intro σ _
  rw [Finset.prod_const]
  change f σ ^ (Finset.univ.filter (fun j => g j = σ)).card = _
  rw [a.2 σ]
