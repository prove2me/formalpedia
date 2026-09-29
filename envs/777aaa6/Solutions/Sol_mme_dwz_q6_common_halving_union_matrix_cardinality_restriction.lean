-- Prove2me | solution 1 for mme_dwz_q6_common_halving_union_matrix_cardinality_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:10:16.039394+00:00
-- url     : https://prove2.me/submissions/22f70ac4-9546-4e06-ad76-5103a2dea192

import Theorems.Thm_mme_dwz_q6_common_halving_union_trace_projection_restriction
import Theorems.Thm_mme_paired_matrix_cartesian_word_projection_extraction

open MME MME.DWZComponentRestriction PiTensorProduct Module TensorProduct BigOperators
universe u
set_option autoImplicit false

/-- The common-halving word unions extract a matrix block from the literal
restricted component pair, with dimensions equal to their word cardinalities. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let h0 := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (6 + 6))) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨finSumFinEquiv.symm (PowIndex.get N w r).down.2⟩ : ULift.{u} (Fin 6 ⊕ Fin 6)))
    let h1 := fun w : PowIndex (ULift.{u} (Fin (6 + 6) × Fin 1)) N ↦
      PowIndex.ofFun N (fun r ↦
        (⟨Sum.swap (finSumFinEquiv.symm (PowIndex.get N w r).down.1)⟩ :
          ULift.{u} (Fin 6 ⊕ Fin 6)))
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    let keepX := fun w : PowIndex (ULift.{u} (Fin 1 × Fin (6 + 6))) N ↦
      ∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N (h0 w) r) =
          (family.entry p).val 0 (halving.position (Sum.inl r))
    let keepY := fun w : PowIndex (ULift.{u} (Fin (6 + 6) × Fin 1)) N ↦
      ∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N (h1 w) r) =
          (family.entry p).val 1 (halving.position (Sum.inr r))
    letI : DecidablePred keepX := Classical.decPred _
    letI : DecidablePred keepY := Classical.decPred _
    TensorObj.Restrict
      (MMObj K (Fintype.card {x // keepX x}) 1 (Fintype.card {y // keepY y}))
      (componentPairRestricted K s m) := by
  intro h0 h1 grade keepX keepY
  let U := TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K 1 (6 + 6) 1)
  let V := TensorObj.permObj cyclicPerm (MMObj K 1 (6 + 6) 1)
  let c : Basis (ULift.{u} (Fin 1 × Fin (6 + 6))) K (Fin 1 × Fin (6 + 6) → K) :=
    (Pi.basisFun K (Fin 1 × Fin (6 + 6))).reindex Equiv.ulift.symm
  let e : Basis (ULift.{u} (Fin (6 + 6) × Fin 1)) K (Fin (6 + 6) × Fin 1 → K) :=
    (Pi.basisFun K (Fin (6 + 6) × Fin 1)).reindex Equiv.ulift.symm
  classical
  letI : DecidablePred keepX := Classical.decPred _
  letI : DecidablePred keepY := Classical.decPred _
  have htrace := mme_dwz_q6_common_halving_union_trace_projection_restriction
    (K := K) s hs m hN family halving
  have hextract := mme_paired_matrix_cartesian_word_projection_extraction
    (K := K) (6 + 6) N keepX keepY
  let B := (kronPowModeBasis U 2 c N).tensorProduct (kronPowModeBasis V 2 e N)
  let allowed := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ×
      PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ↦
    (∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N w.1 r) =
        (family.entry p).val 0 (halving.position (Sum.inl r))) ∧
    (∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N w.2 r) =
        (family.entry p).val 1 (halving.position (Sum.inr r)))
  letI : DecidablePred allowed := Classical.decPred _
  have hp : B.constr K (fun w ↦ if keepX w.1 ∧ keepY w.2 then B w else 0) =
      B.constr K (fun w ↦ if allowed (h0 w.1, h1 w.2) then B w else 0) := by
    apply B.ext
    intro w
    simp only [Basis.constr_basis]
    have hh : (keepX w.1 ∧ keepY w.2) ↔ allowed (h0 w.1, h1 w.2) := Iff.rfl
    exact if_congr hh rfl rfl
  dsimp only at hextract htrace
  erw [hp] at hextract
  exact hextract.trans htrace

#print axioms solution
