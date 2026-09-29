-- Prove2me | solution 1 for mme_dwz_fourth_square_row_ledger_prescribedZ_adapter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T17:36:16.57299+00:00
-- url     : https://prove2.me/submissions/3d72ab6f-aa3e-4226-bec2-f929c47ac3e9

import Definitions.Def_mme_dwz_fourth_q5_180_endpoint_bundle_data
import Definitions.Def_mme_dwz_component_word_projection

open MME
open MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthPrescribedZ181
open MME.StothersFourth MME.DWZComponentRestriction
open Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace MME.DWZRowAdapterSq

theorem mpr_heq {α β : Sort _} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by
  subst h; rfl

theorem mp_heq' {α β : Sort _} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  subst h; rfl

theorem data_basis_heq (K : Type u) [Field K] (i : Fin 180) :
    HEq ((OneHotActualCanonical.componentData K).basis i)
      (OneHotActualCanonical.canonicalAddressZBasis K (componentSpecAt i).address) := by
  unfold OneHotActualCanonical.componentData
  dsimp only
  exact (mpr_heq _ _).trans (mpr_heq _ _)

theorem value_mono {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (b : Basis ι K (T.V 2)) (g : ι → Fin t) (p : IntegerZSplitProfile t) (τ V W : ℝ)
    (hW : 0 ≤ W) (hWV : W ≤ V) (h : HasPrescribedZSixRestrictionValueAtLeast T b g p τ V) :
    HasPrescribedZSixRestrictionValueAtLeast T b g p τ W :=
  ⟨hW, fun v hv hvW ↦ h.2 v hv (lt_of_lt_of_le hvW hWV)⟩

/-- The prescribed-Z value depends on tensor, basis, grade and profile only up to `HEq`. -/
theorem pz_transport2 {K : Type u} [Field K] {T T' : TensorObj K 3} (hT : T = T') {ι ι' : Type u}
    {t t' : ℕ} (b : Basis ι K (T.V 2)) (b' : Basis ι' K (T'.V 2)) (g : ι → Fin t) (g' : ι' → Fin t')
    (p : IntegerZSplitProfile t) (p' : IntegerZSplitProfile t')
    (hι : ι = ι') (ht : t = t') (hb : HEq b b') (hg : HEq g g') (hp : HEq p p') (τ V : ℝ) :
    HasPrescribedZSixRestrictionValueAtLeast T b g p τ V ↔
      HasPrescribedZSixRestrictionValueAtLeast T' b' g' p' τ V := by
  subst hT; subst hι; subst ht
  cases eq_of_heq hb; cases eq_of_heq hg; cases eq_of_heq hp
  rfl

theorem ledgerFin_val (i : Fin 180) : ledgerFin i.val = i.castSucc := by
  apply Fin.ext
  change i.val % 181 = i.val
  exact Nat.mod_eq_of_lt (lt_trans i.isLt (by norm_num))

theorem index_eq {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (j : Fin 180) :
    extendedLedgerIndex data j.castSucc = data.ι j := by
  simp only [extendedLedgerIndex, Fin.lastCases_castSucc]

theorem width_eq (j : Fin 180) :
    ledgerZWidth j.castSucc = (componentSpecAt j).address.zWidth := by
  simp only [ledgerZWidth, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta]

theorem basis_heq {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (j : Fin 180) :
    HEq ((extendLedgerBasisGradeData data).basis j.castSucc) (data.basis j) := by
  simp only [extendLedgerBasisGradeData, Fin.lastCases_castSucc]
  exact mpr_heq _ _

theorem grade_heq {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (j : Fin 180) :
    HEq ((extendLedgerBasisGradeData data).grade j.castSucc) (data.grade j) := by
  simp only [extendLedgerBasisGradeData, Fin.lastCases_castSucc]
  apply Function.hfunext (index_eq data j)
  intro a a' haa'
  refine (mpr_heq _ _).trans ?_
  rw [eq_of_heq ((mp_heq' _ a).trans haa')]

theorem profile_heq (j : Fin 180) :
    HEq (ledgerZProfile j.castSucc) (componentZProfile j) := by
  unfold ledgerZProfile
  rw [dif_pos (show (j.castSucc : ℕ) < 180 from j.isLt)]
  refine (mpr_heq _ _).trans ?_
  rfl

theorem value_iff_generic {K : Type u} [Field K] {tensorAt : Fin 181 → TensorObj K 3}
    (data : ComponentBasisGradeData tensorAt) (i : Fin 180) (τ V : ℝ) :
    LedgerPrescribedZValue (exactLedgerPrescribedZData (extendLedgerBasisGradeData data))
        i.val τ V ↔
      HasPrescribedZSixRestrictionValueAtLeast (tensorAt i.castSucc) (data.basis i)
        (data.grade i) (componentZProfile i) τ V := by
  unfold LedgerPrescribedZValue
  rw [ledgerFin_val]
  exact pz_transport2 rfl _ _ _ _ _ _ (index_eq data i) (width_eq i)
    (basis_heq data i) (grade_heq data i) (profile_heq i) τ V

theorem basis_mpr_coe {K : Type u} [Field K] {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V]
    {S T : Submodule K V} (h : S = T) (e : Basis ι K T = Basis ι K S) (B : Basis ι K S) (x : ι) :
    ((Eq.mpr e B : Basis ι K T) x : V) = (B x : V) := by
  subst h
  rfl

theorem coarseClassBasis_coe (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (c : Fin 5) (p : CoarsePair q c) :
    ((coarseClassBasis (K := K) q i c p : (cwSquareCanonicalGrading K q).classOf i c) :
        (TensorObj.kron (CWObj K q) (CWObj K q)).V i) =
      cwSquareCanonicalBasis K q i p.1 := by
  have hS : Submodule.span K (Set.range fun p : CoarsePair q c ↦ cwSquareCanonicalBasis K q i p.1) =
      Submodule.span K (cwSquareCanonicalBasis K q i '' {p | cwSquarePairGrade q p = c}) := by
    congr 1
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  unfold coarseClassBasis
  simp only [id]
  exact (basis_mpr_coe hS _ _ p).trans (Basis.span_apply _ p)

theorem square_fiber_eq (K : Type u) [Field K] (L : Fin 5) :
    OneHotActualCanonical.gradeFiberBasis (cwSquareCanonicalBasis K 5 2) (cwSquarePairGrade 5) L =
      coarseClassBasis (K := K) 5 2 L := by
  apply Basis.eq_of_apply_eq
  intro p
  apply Subtype.ext
  refine Eq.trans ?_ (coarseClassBasis_coe K 5 2 L p).symm
  simp only [OneHotActualCanonical.gradeFiberBasis, Basis.map_apply,
    LinearEquiv.coe_ofEq_apply, Basis.span_apply]

theorem square_basis_heq (K : Type u) [Field K] (I J L : Fin 5) :
    HEq (OneHotActualCanonical.canonicalAddressZBasis K (.square I J L))
      ((coarseClassBasis (K := K) 5 2 L).reindex Equiv.ulift.symm) := by
  unfold OneHotActualCanonical.canonicalAddressZBasis
  dsimp only
  show HEq ((OneHotActualCanonical.gradeFiberBasis (cwSquareCanonicalBasis K 5 2) (cwSquarePairGrade 5) L).reindex
    Equiv.ulift.symm) ((coarseClassBasis (K := K) 5 2 L).reindex Equiv.ulift.symm)
  rw [square_fiber_eq]
  exact HEq.rfl

theorem tensor_eq_sq (K : Type u) [Field K] (i : Fin 180) (I J L : Fin 5)
    (haddr : (componentSpecAt i).address = .square I J L) :
    tensorAt (canonicalQ5Components K) i.castSucc =
      (cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType I J L) := by
  have hindex : i.castSucc = componentLedgerIndex i := by
    apply Fin.ext
    rfl
  rw [hindex, tensorAt_component, haddr]
  rfl

/-- **Generic square-row adapter.** A prescribed-Z value of the literal square component
`T_{I,J,L}` with its canonical coarse-class Z basis and left fine grade, at the row's own ledger
profile, gives the row's ledger prescribed-Z endpoint at any smaller rate. -/
theorem square_row (K : Type u) [Field K] (i : Fin 180) (I J L : Fin 5)
    (haddr : (componentSpecAt i).address = .square I J L)
    (p : IntegerZSplitProfile 3) (hp : HEq (componentZProfile i) p) (τ V W : ℝ)
    (hW : 0 ≤ W) (hWV : W ≤ V)
    (h : HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType I J L))
      ((coarseClassBasis (K := K) 5 2 L).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade p τ V) :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) i.val τ W := by
  refine (value_iff_generic (OneHotActualCanonical.componentData K) i τ W).mpr ?_
  refine (pz_transport2 (tensor_eq_sq K i I J L haddr) _ _ _ _ _ _ ?_ ?_ ?_ ?_ hp τ W).mpr
    (value_mono _ _ _ _ τ V W hW hWV h)
  · show OneHotActualCanonical.CanonicalAddressZIndex K (componentSpecAt i).address = _
    rw [haddr]
    rfl
  · show (componentSpecAt i).address.zWidth = 3
    rw [haddr]
    rfl
  · exact (data_basis_heq K i).trans
      ((congr_arg_heq (OneHotActualCanonical.canonicalAddressZBasis K) haddr).trans
        (square_basis_heq K I J L))
  · exact (congr_arg_heq (OneHotActualCanonical.canonicalAddressZGrade K) haddr).trans HEq.rfl
end MME.DWZRowAdapterSq

theorem solution (K : Type u) [Field K] (i : Fin 180)
    (I J L : Fin 5) (haddr : (componentSpecAt i).address = .square I J L)
    (p : IntegerZSplitProfile 3) (hp : HEq (componentZProfile i) p) (τ V W : ℝ)
    (hW : 0 ≤ W) (hWV : W ≤ V)
    (h : HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType I J L))
      ((coarseClassBasis (K := K) 5 2 L).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade p τ V) :
    LedgerPrescribedZValue (DWZFourthQ5EndpointBundle.ledgerData K) i.val τ W :=
  MME.DWZRowAdapterSq.square_row K i I J L haddr p hp τ V W hW hWV h
