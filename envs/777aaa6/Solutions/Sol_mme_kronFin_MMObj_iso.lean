-- Prove2me | solution 1 for mme_kronFin_MMObj_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:25:06.411972+00:00
-- url     : https://prove2.me/submissions/78f3b0dd-8bd6-4207-9c2d-472584bcebdb

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_tensor_bridge

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K] :
    ∀ (R : ℕ) (a b c : Fin R → ℕ),
      TensorObj.Isomorphic
        (TensorObj.kronFin R (fun r => MMObj K (a r) (b r) (c r)))
        (MMObj K (∏ r, a r) (∏ r, b r) (∏ r, c r)) := by
  intro R
  induction R with
  | zero =>
      intro a b c
      simp only [TensorObj.kronFin, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, pow_zero]
      have hq :
          TensorQ.toQ (TensorObj.oneObj : TensorObj K 3) =
            TensorQ.toQ (MMObj K 1 1 1) := by
        exact (MMq_one (K := K)).symm
      exact Quotient.exact hq
  | succ R ih =>
      intro a b c
      let af : Fin R → ℕ := fun r => a r.succ
      let bf : Fin R → ℕ := fun r => b r.succ
      let cf : Fin R → ℕ := fun r => c r.succ
      have htail := ih af bf cf
      have hkron : TensorObj.Isomorphic
          (TensorObj.kron (MMObj K (a 0) (b 0) (c 0))
            (TensorObj.kronFin R
              (fun r => MMObj K (af r) (bf r) (cf r))))
          (TensorObj.kron (MMObj K (a 0) (b 0) (c 0))
            (MMObj K (∏ r, af r) (∏ r, bf r) (∏ r, cf r))) :=
        TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _) htail
      have hmm := MMObj_kron_iso (K := K)
        (a 0) (b 0) (c 0)
        (∏ r, af r) (∏ r, bf r) (∏ r, cf r)
      simpa only [TensorObj.kronFin, af, bf, cf, Fin.prod_univ_succ] using
        hkron.trans hmm

