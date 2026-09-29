-- Prove2me | solution 1 for mme_dwz_q6_common_halving_shared_Z_star_source_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:53:04.921757+00:00
-- url     : https://prove2.me/submissions/1c052186-a933-4b66-b93b-3feb9eb393ec

import Theorems.Thm_mme_primary_hash_family_masked_outer_extraction_map
import Theorems.Thm_mme_dwz_q6_common_halving_aligned_filtered_source_restriction
import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction MME.CompleteSplit112
open Module PiTensorProduct CoupledCTensorPackaging
universe u
set_option autoImplicit false

private theorem filtered_stars_restrict
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (M : ℕ) (hM : 2 * N = M) :
    let T := (coupledObj K 6).kronPow M
    let b := (Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm
    let bX := kronPowModeBasis (coupledObj K 6) 0 b M
    let bY := kronPowModeBasis (coupledObj K 6) 1 b M
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x => Sum.elim (fun _ => 0) (fun _ => 1) x.down
    let keepX := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) M =>
      ∃ p : Fin A × Fin H, ∀ r : Fin N,
        grade (PowIndex.get M w (Fin.cast hM (halving.position (Sum.inl r)))) =
          (family.entry p).val 0 (halving.position (Sum.inl r))
    let keepY := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) M =>
      ∃ p : Fin A × Fin H, ∀ r : Fin N,
        grade (PowIndex.get M w (Fin.cast hM (halving.position (Sum.inr r)))) =
          (family.entry p).val 1 (halving.position (Sum.inr r))
    letI : DecidablePred keepX := Classical.decPred _
    letI : DecidablePred keepY := Classical.decPred _
    let f : ∀ i, T.V i →ₗ[K] T.V i := Function.update
      (Function.update (fun _ => LinearMap.id) 0
        (bX.constr K (fun w => if keepX w then bX w else 0))) 1
      (bY.constr K (fun w => if keepY w then bY w else 0))
    TensorObj.Restrict (TensorObj.bigAdd (starObj (grading K 6) family))
      { T with t := PiTensorProduct.map f T.t } := by
  subst M
  intro T b bX bY grade keepX keepY f
  letI : DecidablePred keepX := Classical.decPred _
  letI : DecidablePred keepY := Classical.decPred _
  let keep : ∀ i, PowIndex (LiftedCoord.{u} 6 i) (2 * N) → Prop
    | ⟨0, _⟩ => keepX
    | ⟨1, _⟩ => keepY
    | ⟨2, _⟩ => fun _ => True
  letI (i : Fin 3) : DecidablePred (keep i) := Classical.decPred _
  have hzero (i : Fin 3) (a : Fin 3) (j : LiftedCoord.{u} 6 i)
      (hne : liftedCoordGrade 6 i j ≠ a) :
      (grading K 6).blockProj i a (liftedCoordBasis K 6 i j) = 0 :=
    TensorObj.TypeGrading.blockProj_apply_mem_ne (grading K 6) i a
      (liftedCoordGrade 6 i j) hne.symm _
      ((mme_complete_split_112_coupled_basis_label_certificate K 6).2.2.2 i j)
  have hg0 (x : ULift.{u} (Fin 6 ⊕ Fin 6)) : liftedCoordGrade 6 0 x = grade x := by
    rcases x with ⟨x⟩
    cases x <;> rfl
  have hg1 (x : ULift.{u} (Fin 6 ⊕ Fin 6)) : liftedCoordGrade 6 1 x = grade x := by
    rcases x with ⟨x⟩
    cases x <;> rfl
  have hkeep (a : Fin A) (h : Fin H) (i : Fin 3)
      (w : PowIndex (LiftedCoord.{u} 6 i) (2 * N))
      (hw : ∀ r, liftedCoordGrade 6 i (PowIndex.get (2 * N) w r) =
        componentAddress family a h i r) : keep i w := by
    fin_cases i
    · refine ⟨(a, h), ?_⟩
      intro r
      have hr := hw (halving.position (Sum.inl r))
      change liftedCoordGrade 6 0 _ = componentAddress family a h 0 _ at hr
      rw [hg0, componentAddress_eq_entry] at hr
      exact hr
    · refine ⟨(a, h), ?_⟩
      intro r
      have hr := hw (halving.position (Sum.inr r))
      change liftedCoordGrade 6 1 _ = componentAddress family a h 1 _ at hr
      rw [hg1, componentAddress_eq_entry] at hr
      exact hr
    · trivial
  have hmap := mme_primary_hash_family_masked_outer_extraction_map
    (grading K 6) family
    (mme_complete_split_112_concrete_four_block_certificate (K := K) 6).1
    (liftedCoordBasis K 6) (liftedCoordGrade 6) hzero keep hkeep
  let mask := fun i => (kronPowModeBasis (coupledObj K 6) i (liftedCoordBasis K 6 i)
    (2 * N)).constr K (fun w => if keep i w then
      kronPowModeBasis (coupledObj K 6) i (liftedCoordBasis K 6 i) (2 * N) w else 0)
  have hf : mask = f := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · apply (kronPowModeBasis (coupledObj K 6) 2 (liftedCoordBasis K 6 2) (2 * N)).ext
      intro w
      change (kronPowModeBasis (coupledObj K 6) 2 (liftedCoordBasis K 6 2)
        (2 * N)).constr K _ _ = _
      rw [Basis.constr_basis, if_pos (show keep 2 w from trivial)]
      rfl
  refine ⟨outerExtractionMap (grading K 6) family, ?_⟩
  change PiTensorProduct.map (outerExtractionMap (grading K 6) family)
    (PiTensorProduct.map f T.t) = _
  rw [← hf]
  exact hmap

/-- The actual DWZ six-symmetrized source supplies the cyclic symmetrization
of the original family's shared-Z stars. -/
theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    TensorObj.Restrict
      (cyclicSymmetrization (TensorObj.bigAdd (starObj (grading K 6) family)))
      (sixSymmetrization (restrictedComponentPower K s m)) := by
  have hsource := mme_dwz_q6_common_halving_aligned_filtered_source_restriction
    (K := K) s hs m hN family halving
  exact (mme_cyclicSymmetrization_mono_restrict
    (filtered_stars_restrict (K := K) family halving (N + N) (by omega))).trans hsource

#print axioms solution
