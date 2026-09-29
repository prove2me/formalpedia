-- Prove2me | solution 1 for mme_CW_q6_common_halving_fiber_direct_sum_assembly_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:41:29.062219+00:00
-- url     : https://prove2.me/submissions/c2f28c2a-a20f-43f6-aa31-e78924961dcb

import Theorems.Thm_mme_direct_sum_component_assembly_iff_mixed_vanishing
import Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
import Theorems.Thm_mme_CW_q6_common_halving_fiber_paired_induced_iff

open MME MME.PairedOrientedPackaging PiTensorProduct BigOperators
universe u
set_option autoImplicit false

/-- Projecting a tensor power along an address gives exactly the ordered
Kronecker product of its coordinate blocks. -/
private theorem map_gradedAddressProj
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (a : Fin 3 → Fin N → Fin t) :
    PiTensorProduct.map (gradedAddressProj G N a) (T.kronPow N).t =
      (gradedAddressBlock G a).t := by
  induction N with
  | zero =>
      change PiTensorProduct.map (fun _ => LinearMap.id)
          (TensorObj.oneObj : TensorObj K 3).t =
        (TensorObj.oneObj : TensorObj K 3).t
      rw [PiTensorProduct.map_id]
      rfl
  | succ N ih =>
      change PiTensorProduct.map
          (fun i => TensorProduct.map
            (G.blockProj i (a i 0))
            (gradedAddressProj G N (fun i j => a i j.succ) i))
          (interchange T.t (T.kronPow N).t) =
        interchange
          (G.blockTensor (fun i => a i 0))
          (gradedAddressBlock G (fun i j => a i j.succ)).t
      rw [TensorObj.TypeGrading.kronMap_interchange]
      unfold TensorObj.TypeGrading.blockTensor
      rw [ih]


/-- The literal sum of all component maps in one color is a direct-sum
extraction exactly when both half-pattern functions separately are injective. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) :
    let T := TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
    let B := fun h : Fin H => componentObj (K := K) family halving (a,h)
    PiTensorProduct.map (fun i => ∑ h : Fin H,
      (gradedBigAddSlot H B h i).comp (componentProj family halving (a,h) i)) T.t =
        (TensorObj.bigAdd B).t ↔
      Function.Injective (fun h : Fin H => fun r : Fin N =>
        (family.entry (a,h)).val 0 (halving.position (Sum.inl r))) ∧
      Function.Injective (fun h : Fin H => fun r : Fin N =>
        (family.entry (a,h)).val 1 (halving.position (Sum.inr r))) := by
  intro T B
  have hdiag (h : Fin H) :
      PiTensorProduct.map (componentProj (K := K) family halving (a,h)) T.t =
        (B h).t := by
    change PiTensorProduct.map
      (fun i => TensorProduct.map
        (gradedAddressProj (leftGrading (K := K)) N
          (leftAddress family halving (a,h)) i)
        (gradedAddressProj (rightGrading (K := K)) N
          (rightAddress family halving (a,h)) i))
      (interchange _ _) = interchange _ _
    rw [TensorObj.TypeGrading.kronMap_interchange,
      map_gradedAddressProj, map_gradedAddressProj]
  rw [mme_direct_sum_component_assembly_iff_mixed_vanishing T B
    (fun h i => componentProj family halving (a,h) i) hdiag,
    ← mme_CW_q6_common_halving_fiber_paired_induced_iff family halving a]
  constructor
  · intro hzero h0 h1 h2 hs
    by_contra hbad
    have hnot : ¬ ∃ h : Fin H, ![h0,h1,h2] = fun _ => h := by
      rintro ⟨h, he⟩
      apply hbad
      exact ⟨(congrFun he 0).trans (congrFun he 1).symm,
        (congrFun he 1).trans (congrFun he 2).symm⟩
    have hn := (mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
      (K := K) family halving (fun i => (a, ![h0,h1,h2] i))).mpr hs
    exact hn (hzero ![h0,h1,h2] hnot)
  · intro hi js hnot
    by_contra hn
    have hs := (mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
      (K := K) family halving (fun i => (a, js i))).mp hn
    obtain ⟨h01, h12⟩ := hi (js 0) (js 1) (js 2) hs
    apply hnot
    refine ⟨js 0, funext fun i => ?_⟩
    fin_cases i <;> simp_all

#print axioms solution
