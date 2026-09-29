-- Prove2me | solution 1 for mme_CW_coupled_cyclic_high_MM_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:55:25.808992+00:00
-- url     : https://prove2.me/submissions/e4a6d48a-68ab-46e9-a2eb-79268acf7e2d

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_permutation

open MME PiTensorProduct

universe u


namespace CWCoupledCyclicHighMM

theorem cyclic_eq_public
    {K : Type u} [Field K] (X : TensorObj K 3) :
    cyclicSymmetrization X =
      TensorObj.kron X
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm X)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)) := by
  unfold cyclicSymmetrization
  congr 3 <;> apply Equiv.ext <;> intro i <;> fin_cases i <;> rfl

theorem permObj_trans_iso
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj (e.trans e') X)
      (TensorObj.permObj e' (TensorObj.permObj e X)) := by
  have ht :
      (TensorObj.permObj (e.trans e') X).t =
        (TensorObj.permObj e' (TensorObj.permObj e X)).t := by
    show (PiTensorProduct.reindex K X.V (e.trans e')) X.t =
      (PiTensorProduct.reindex K (fun i => X.V (e.symm i)) e')
        ((PiTensorProduct.reindex K X.V e) X.t)
    exact (PiTensorProduct.reindex_reindex e e' X.t).symm
  refine ⟨⟨fun _ => LinearMap.id, ?_⟩, ⟨fun _ => LinearMap.id, ?_⟩⟩
  · rw [ht]
    induction (TensorObj.permObj e' (TensorObj.permObj e X)).t using
        PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp only [map_smul, LinearMap.smul_apply, PiTensorProduct.map_tprod]
        congr 2
    | add x y ihx ihy =>
        simp only [map_add, ihx, ihy]
        rfl
  · rw [← ht]
    induction (TensorObj.permObj (e.trans e') X).t using
        PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp only [map_smul, LinearMap.smul_apply, PiTensorProduct.map_tprod]
        congr 2
    | add x y ihx ihy =>
        simp only [map_add, ihx, ihy]
        rfl

theorem second_cyclic_MM_iso
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K q 1 q))
      (MMObj K 1 q q) := by
  refine TensorObj.Isomorphic.trans
    (permObj_trans_iso cyclicPerm cyclicPerm (MMObj K q 1 q)) ?_
  refine TensorObj.Isomorphic.trans
    (TensorObj.permObj_isomorphic cyclicPerm
      (MMObj_permObj_cyclic q 1 q)) ?_
  exact MMObj_permObj_cyclic q q 1

theorem nested_MM_iso
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kron (MMObj K q 1 q)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (MMObj K q 1 q))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (MMObj K q 1 q))))
      (MMObj K (q * q) (q * q) (q * q)) := by
  have hcyc₁ : TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm (MMObj K q 1 q))
      (MMObj K q q 1) := MMObj_permObj_cyclic q 1 q
  have hcyc₂ : TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K q 1 q))
      (MMObj K 1 q q) := second_cyclic_MM_iso q
  have hblocks : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K q 1 q)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (MMObj K q 1 q))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (MMObj K q 1 q))))
      (TensorObj.kron (MMObj K q 1 q)
        (TensorObj.kron (MMObj K q q 1) (MMObj K 1 q q))) :=
    TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _)
      (TensorQ.mul_respects_iso hcyc₁ hcyc₂)
  have hinner : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K q q 1) (MMObj K 1 q q))
      (MMObj K (q * 1) (q * q) (1 * q)) :=
    MMObj_kron_iso q q 1 1 q q
  have hcombine : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K q 1 q)
        (TensorObj.kron (MMObj K q q 1) (MMObj K 1 q q)))
      (TensorObj.kron (MMObj K q 1 q)
        (MMObj K (q * 1) (q * q) (1 * q))) :=
    TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _) hinner
  have houter : TensorObj.Isomorphic
      (TensorObj.kron (MMObj K q 1 q)
        (MMObj K (q * 1) (q * q) (1 * q)))
      (MMObj K (q * (q * 1)) (1 * (q * q)) (q * (1 * q))) :=
    MMObj_kron_iso q 1 q (q * 1) (q * q) (1 * q)
  refine TensorObj.Isomorphic.trans hblocks
    (TensorObj.Isomorphic.trans hcombine ?_)
  simpa using houter

end CWCoupledCyclicHighMM

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K (q * q) (q * q) (q * q))
      (cyclicSymmetrization (MMObj K q 1 q)) := by
  rw [CWCoupledCyclicHighMM.cyclic_eq_public]
  exact (CWCoupledCyclicHighMM.nested_MM_iso q).2
