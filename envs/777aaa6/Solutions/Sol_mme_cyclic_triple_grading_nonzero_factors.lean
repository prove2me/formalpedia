-- Prove2me | solution 1 for mme_cyclic_triple_grading_nonzero_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:35:32.675362+00:00
-- url     : https://prove2.me/submissions/d55c7bea-31a5-4118-a32c-7683ce06d2f6

import Definitions.Def_mme_cyclic_triple_grading

open MME TensorObj.TypeGrading

universe u

set_option autoImplicit false

private theorem gradingOfEq_blockTensor_ne_zero_iff
    {K : Type u} [Field K] {d t : Nat}
    {A B : TensorObj K d} (h : A = B)
    (G : B.TypeGrading t) (rho : Fin d -> Fin t) :
    (mmeGradingOfEq h G).blockTensor rho ≠ 0 ↔
      G.blockTensor rho ≠ 0 := by
  subst B
  rfl

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t : Nat}
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 -> Fin t)
    (h : (mmeCyclicTripleGrading G).blockTensor
      (mmeCyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    G.blockTensor rhoX ≠ 0 /\
      G.blockTensor rhoY ≠ 0 /\
      G.blockTensor rhoZ ≠ 0 := by
  have htransport :
      (mmePublicCyclicTripleGrading G).blockTensor
          (mmeCyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 := by
    exact (gradingOfEq_blockTensor_ne_zero_iff
      (cyclicSymmetrization_eq_public_perm T)
      (mmePublicCyclicTripleGrading G)
      (mmeCyclicTripleGrade rhoX rhoY rhoZ)).mp h
  have hx : G.blockTensor rhoX ≠ 0 :=
    kronGrading_blockTensor_ne_zero_left G
      (kronGrading
        (permObjGrading G cyclicPerm)
        (permObjGrading G (cyclicPerm.trans cyclicPerm)))
      rhoX
      (fun i => finProdFinEquiv
        (rhoY (cyclicPerm.symm i),
          rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) htransport
  have hinner := kronGrading_blockTensor_ne_zero_right G
    (kronGrading
      (permObjGrading G cyclicPerm)
      (permObjGrading G (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i => finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) htransport
  have hyPerm := kronGrading_blockTensor_ne_zero_left
    (permObjGrading G cyclicPerm)
    (permObjGrading G (cyclicPerm.trans cyclicPerm))
    (fun i => rhoY (cyclicPerm.symm i))
    (fun i => rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  have hzPerm := kronGrading_blockTensor_ne_zero_right
    (permObjGrading G cyclicPerm)
    (permObjGrading G (cyclicPerm.trans cyclicPerm))
    (fun i => rhoY (cyclicPerm.symm i))
    (fun i => rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  have hy : G.blockTensor rhoY ≠ 0 := by
    intro hy0
    apply hyPerm
    rw [permObjGrading_blockTensor G cyclicPerm rhoY, hy0, map_zero]
    rfl
  have hz : G.blockTensor rhoZ ≠ 0 := by
    intro hz0
    apply hzPerm
    rw [permObjGrading_blockTensor G
      (cyclicPerm.trans cyclicPerm) rhoZ, hz0, map_zero]
    rfl
  exact ⟨hx, hy, hz⟩
