-- Prove2me | solution 1 for mme_schonhage_pan_targetTensor_repr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:02:13.084273+00:00
-- url     : https://prove2.me/submissions/ed3d5e9d-51b0-4627-a033-2cc10cc401f2

import Definitions.Def_mme_schonhage_pan_certificate

open MME PiTensorProduct BigOperators Finset Polynomial

universe u

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

variable {K : Type u} [Field K]

noncomputable section

private lemma tensorBasis_tprod_repr
    (x : ∀ r, (PanLeanBridge.Xobj (K := K)).V r)
    (q : (r : Fin 3) → PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr (tprod K x) q =
      ∏ r, (PanLeanBridge.modeBasis (K := K) r).repr (x r) (q r) := by
  exact Basis.piTensorProduct_repr_tprod_apply _ _ _

private lemma single_one_delta {A : Type*} [DecidableEq A] (a q : A) :
    (Finsupp.single a (1 : K)) q = PanLeanBridge.delta (K := K) q a := by
  rw [Finsupp.single_apply]
  simp [PanLeanBridge.delta, eq_comm]

private lemma pureABC_repr (s : Fin 2) (i : Fin 5) (k : Fin 11)
    (q : ∀ r : Fin 3, PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr
        (PanLeanBridge.pureABC (K := K) s i k) q =
      PanLeanBridge.ac (K := K) (q 0) s i *
        PanLeanBridge.cc (K := K) (q 1) s k i *
        PanLeanBridge.bc (K := K) (q 2) s k := by
  unfold PanLeanBridge.pureABC
  rw [tensorBasis_tprod_repr]
  simp only [Fin.prod_univ_three, Module.Basis.repr_self]
  simp_rw [single_one_delta]
  fin_cases s <;>
    simp [PanLeanBridge.ac, PanLeanBridge.cc, PanLeanBridge.bc,
      PanLeanBridge.sideSign] <;> rfl

private lemma pureUWV_repr (s : Fin 2) (i : Fin 5) (k : Fin 11)
    (q : ∀ r : Fin 3, PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr
        (PanLeanBridge.pureUWV (K := K) s i k) q =
      PanLeanBridge.uc (K := K) (q 0) s k *
        PanLeanBridge.wc (K := K) (q 1) s i *
        PanLeanBridge.vc (K := K) (q 2) k i := by
  unfold PanLeanBridge.pureUWV
  rw [tensorBasis_tprod_repr]
  simp only [Fin.prod_univ_three, Module.Basis.repr_self]
  simp_rw [single_one_delta]
  rfl

private lemma pureXZY_repr (s : Fin 2) (i : Fin 5) (k : Fin 11)
    (q : ∀ r : Fin 3, PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr
        (PanLeanBridge.pureXZY (K := K) s i k) q =
      PanLeanBridge.xc (K := K) (q 0) s k i *
        PanLeanBridge.zc (K := K) (q 1) k *
        PanLeanBridge.yc (K := K) (q 2) s i := by
  unfold PanLeanBridge.pureXZY
  rw [tensorBasis_tprod_repr]
  simp only [Fin.prod_univ_three, Module.Basis.repr_self]
  simp_rw [single_one_delta]
  rfl

theorem solution
    {K : Type u} [Field K]
    (q : ∀ r : Fin 3, PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr
        (PanLeanBridge.targetTensor (K := K)) q =
      ∑ s : Fin 2,
        PanLeanBridge.targetSide (K := K) (q 0) (q 1) (q 2) s := by
  simp [PanLeanBridge.targetTensor, PanLeanBridge.targetSide,
    pureABC_repr, pureUWV_repr, pureXZY_repr]

end
