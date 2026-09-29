-- Prove2me | solution 1 for mme_cyclic_triple_grading_block_subtensor_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:35:32.700751+00:00
-- url     : https://prove2.me/submissions/a28e2958-dbc6-44de-b1f6-217fee962df8

import Definitions.Def_mme_cyclic_triple_grading
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso

open MME TensorObj.TypeGrading

universe u

set_option autoImplicit false

private theorem gradingOfEq_blockSubtensor_iso
    {K : Type u} [Field K] {d t : Nat}
    {A B : TensorObj K d} (h : A = B)
    (G : B.TypeGrading t) (rho : Fin d -> Fin t) :
    TensorObj.Isomorphic
      ((mmeGradingOfEq h G).blockSubtensor rho)
      (G.blockSubtensor rho) := by
  subst B
  exact TensorObj.Isomorphic.refl _

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t : Nat}
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 -> Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (G.blockSubtensor rhoX)
        (TensorObj.kron
          ((permObjGrading G cyclicPerm).blockSubtensor
            (fun i => rhoY (cyclicPerm.symm i)))
          ((permObjGrading G (cyclicPerm.trans cyclicPerm)).blockSubtensor
            (fun i => rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))))
      ((mmeCyclicTripleGrading G).blockSubtensor
        (mmeCyclicTripleGrade rhoX rhoY rhoZ)) := by
  let GY := permObjGrading G cyclicPerm
  let GZ := permObjGrading G (cyclicPerm.trans cyclicPerm)
  let sy : Fin 3 -> Fin t := fun i => rhoY (cyclicPerm.symm i)
  let sz : Fin 3 -> Fin t := fun i =>
    rhoZ ((cyclicPerm.trans cyclicPerm).symm i)
  have hinner := mme_TypeGrading_kron_blockSubtensor_iso GY GZ sy sz
  have hlift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl (G.blockSubtensor rhoX)) hinner
  have houter := mme_TypeGrading_kron_blockSubtensor_iso
    G (kronGrading GY GZ) rhoX
      (fun i => finProdFinEquiv (sy i, sz i))
  have hpublic := hlift.trans houter
  have htransport := gradingOfEq_blockSubtensor_iso
    (cyclicSymmetrization_eq_public_perm T)
    (mmePublicCyclicTripleGrading G)
    (mmeCyclicTripleGrade rhoX rhoY rhoZ)
  exact hpublic.trans htransport.symm
