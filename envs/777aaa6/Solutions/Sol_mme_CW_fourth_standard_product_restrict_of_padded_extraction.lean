-- Prove2me | solution 1 for mme_CW_fourth_standard_product_restrict_of_padded_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T09:25:26.978424+00:00
-- url     : https://prove2.me/submissions/0cb8c499-d8b9-4ce0-9575-27974e2a85a9

import Theorems.Thm_mme_CW_atomic_fourth_component_grouping_projection_transport
import Theorems.Thm_mme_CW_fourth_component_profile_projection_normalization
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
import Theorems.Thm_mme_dwz_prescribed_Z_product_uniform_basis_shuffle
import Theorems.Thm_mme_dwz_generic_basis_label_hole_cover_tensor_repair
import Theorems.Thm_mme_bigAdd_mono_restrict
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj MME.StothersFourth MME.DWZStep1Support MME.DWZSimultaneous
  MME.DWZComponentRestriction MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.DWZSquare Module PiTensorProduct BigOperators
open scoped Classical
universe u v w z
set_option autoImplicit false
set_option maxHeartbeats 1000000

set_option warningAsError true

namespace MME.DWZStandardProductRepairComposition

theorem projection_yes {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) (a : I i) (ha : P i a) :
    ((T.basisAllAllowedGrading b P).blockProj i 0 (b i a) : T.V i) = b i a := by
  classical
  have hm : b i a ∈ (T.basisAllAllowedGrading b P).classOf i 0 := by
    have hs : (T.basisAllAllowedGrading b P).classOf i 0 =
        Submodule.span K (b i '' {a | P i a}) := by
      simp [TensorObj.basisAllAllowedGrading, TensorObj.TypeGrading.classOf, cwBasisGrade]
    rw [hs]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hm]

theorem projection_no {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) (a : I i) (ha : ¬ P i a) :
    (T.basisAllAllowedGrading b P).blockProj i 0 (b i a) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ 1 (by decide)
  apply Submodule.subset_span
  exact ⟨a, by simp [ha], rfl⟩

/-- The actual normalization maps commute with a literal owner mask.  The
router need not be injective: only its basis image and mask covariance matter. -/
theorem owner_projection_normalizes_to_literal
    {K : Type u} [Field K] (T P : TensorObj K 3)
    {I : Fin 3 → Type u} {Coord : Type v} {Block : Type w}
    [DecidableEq Block]
    (b : ∀ i, Basis (I i) K (T.V i)) (B : Basis Coord K (P.V 2))
    (label : Coord → Block) (blocks : Finset Block)
    (base allowed : ∀ i, I i → Prop)
    (route : {a : I 2 // base 2 a} → Coord)
    (f : ∀ i, T.V i →ₗ[K] P.V i)
    (htensor : PiTensorProduct.map f T.t = P.t)
    (hzero : ∀ i a, ¬ base i a → f i (b i a) = 0)
    (hZ : ∀ a (ha : base 2 a), f 2 (b 2 a) = B (route ⟨a, ha⟩))
    (hXY : ∀ i, i ≠ 2 → ∀ a, allowed i a ↔ base i a)
    (hmask : ∀ a, allowed 2 a ↔
      ∃ ha : base 2 a, label (route ⟨a, ha⟩) ∈ blocks) :
    TensorObj.Restrict
      { V := P.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection B label blocks)) P.t }
      (T.basisAllAllowedSubtensor b allowed) := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  let M : ∀ i, P.V i →ₗ[K] P.V i :=
    Function.update (fun _ ↦ LinearMap.id) 2 (basisLabelProjection B label blocks)
  let g : ∀ i, G.classOf i 0 →ₗ[K] P.V i :=
    fun i ↦ (f i).comp (G.classOf i 0).subtype
  have hcomm (i : Fin 3) :
      (g i).comp (G.blockProj i 0) = (M i).comp (f i) := by
    apply (b i).ext
    intro a
    simp only [LinearMap.comp_apply]
    by_cases hi : i = 2
    · subst i
      by_cases ha : base 2 a
      · rw [hZ a ha]
        change f 2 ((G.blockProj 2 0 (b 2 a) : T.V 2)) =
          basisLabelProjection B label blocks (B (route ⟨a, ha⟩))
        simp only [basisLabelProjection, Basis.constr_basis]
        by_cases hh : label (route ⟨a, ha⟩) ∈ blocks
        · rw [if_pos hh, projection_yes T b allowed 2 a ((hmask a).mpr ⟨ha, hh⟩), hZ a ha]
        · have hn : ¬ allowed 2 a := by
            intro h
            obtain ⟨ha', h⟩ := (hmask a).mp h
            exact hh h
          rw [projection_no T b allowed 2 a hn]
          simp [hh]
      · have hn : ¬ allowed 2 a := by
          intro h
          exact ha ((hmask a).mp h).choose
        rw [hzero 2 a ha, map_zero]
        change f 2 ((G.blockProj 2 0 (b 2 a) : T.V 2)) = 0
        rw [projection_no T b allowed 2 a hn]
        simp
    · have hM : M i = LinearMap.id := Function.update_of_ne hi _ _
      rw [hM, LinearMap.id_apply]
      change f i ((G.blockProj i 0 (b i a) : T.V i)) = f i (b i a)
      by_cases ha : base i a
      · rw [projection_yes T b allowed i a ((hXY i hi a).mpr ha)]
      · rw [projection_no T b allowed i a (fun h ↦ ha ((hXY i hi a).mp h)),
          hzero i a ha]
        simp
  refine ⟨g, ?_⟩
  change PiTensorProduct.map g (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t) =
    PiTensorProduct.map M P.t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simp_rw [hcomm]
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, htensor]

/-- The exact interface returned by constituent normalization suffices: compose
its maps with the coarse/profile projection, rather than assume any restriction
for the owner-masked tensor. -/
theorem projected_owner_normalizes_to_literal
    {K : Type u} [Field K] (T P : TensorObj K 3)
    {I : Fin 3 → Type u} {Coord : Type v} {Block : Type w}
    [DecidableEq Block]
    (b : ∀ i, Basis (I i) K (T.V i)) (B : Basis Coord K (P.V 2))
    (label : Coord → Block) (blocks : Finset Block)
    (base allowed : ∀ i, I i → Prop)
    (route : {a : I 2 // base 2 a} → Coord)
    (L : ∀ i, (T.basisAllAllowedGrading b base).classOf i 0 →ₗ[K] P.V i)
    (htensor : PiTensorProduct.map L (T.basisAllAllowedSubtensor b base).t = P.t)
    (hZ : ∀ a (ha : base 2 a),
      L 2 ((T.basisAllAllowedGrading b base).blockProj 2 0 (b 2 a)) =
        B (route ⟨a, ha⟩))
    (hXY : ∀ i, i ≠ 2 → ∀ a, allowed i a ↔ base i a)
    (hmask : ∀ a, allowed 2 a ↔
      ∃ ha : base 2 a, label (route ⟨a, ha⟩) ∈ blocks) :
    TensorObj.Restrict
      { V := P.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection B label blocks)) P.t }
      (T.basisAllAllowedSubtensor b allowed) := by
  let G := T.basisAllAllowedGrading b base
  let f := fun i ↦ (L i).comp (G.blockProj i 0)
  have hf : PiTensorProduct.map f T.t = P.t := by
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    exact htensor
  have hz (i : Fin 3) (a : I i) (ha : ¬ base i a) : f i (b i a) = 0 := by
    change L i (G.blockProj i 0 (b i a)) = 0
    rw [projection_no T b base i a ha, map_zero]
  exact owner_projection_normalizes_to_literal T P b B label blocks base allowed
    route f hf hz hZ hXY hmask

end MME.DWZStandardProductRepairComposition


namespace MME.DWZConcreteRouter

theorem grouped_base_iff
    {C : Type v} [DecidableEq C] {q N R : ℕ}
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → Fin 5 → ℕ) (j : Fin R) (i : Fin 3)
    (n : C → ℕ) (counts : C → Fin 5 → ℕ)
    (hmu : ∀ c a, mu 2 c a = counts c a)
    (positions : Fin N ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, component j (positions.symm ⟨c,r⟩) = c)
    (w : WordIndex.{u} q 3 N)
    (v : ∀ c, Fin (n c) →
      ULift.{u} ((Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2))))
    (hrouter : ∀ c r, let t := positions.symm ⟨c,r⟩
      (v c r).down =
        (((w (finProdFinEquiv (t,0))).down, (w (finProdFinEquiv (t,1))).down),
         ((w (finProdFinEquiv (t,2))).down, (w (finProdFinEquiv (t,3))).down))) :
    (Graded component shape j i (label q 3 N w) ∧
      (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w))) ↔
    ∀ c,
      (∀ r, (cwFourthPairGrade q (v c r).down).val = shape c i) ∧
      (i = 2 → ∀ a : Fin 5,
        (Finset.univ.filter (fun r : Fin (n c) ↦
          cwSquarePairGrade q (v c r).down.1 = a)).card = counts c a) := by
  classical
  have hgrade (c : C) (r : Fin (n c)) :
      (cwFourthPairGrade q (v c r).down).val =
        ∑ s : Fin 4, (label q 3 N w (positions.symm ⟨c,r⟩) s).val := by
    rw [hrouter]
    change ((label q 3 N w (positions.symm ⟨c,r⟩) 0).val +
      (label q 3 N w (positions.symm ⟨c,r⟩) 1).val) +
      ((label q 3 N w (positions.symm ⟨c,r⟩) 2).val +
      (label q 3 N w (positions.symm ⟨c,r⟩) 3).val) = _
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  have htag (c : C) (r : Fin (n c)) :
      cwSquarePairGrade q (v c r).down.1 =
        fourthLeftTag (label q 3 N w (positions.symm ⟨c,r⟩)) := by
    rw [hrouter]
    apply Fin.ext
    rfl
  have hcard (c : C) (a : Fin 5) :
      Fintype.card {t : Fin N // component j t = c ∧
        fourthLeftTag (label q 3 N w t) = a} =
      (Finset.univ.filter (fun r : Fin (n c) ↦
        cwSquarePairGrade q (v c r).down.1 = a)).card := by
    let f : {r : Fin (n c) // cwSquarePairGrade q (v c r).down.1 = a} →
        {t : Fin N // component j t = c ∧ fourthLeftTag (label q 3 N w t) = a} :=
      fun r ↦ ⟨positions.symm ⟨c,r.val⟩, hcell c r.val,
        (htag c r.val).symm.trans r.property⟩
    have hf : Function.Bijective f := by
      constructor
      · intro r s hrs
        apply Subtype.ext
        have hs : (⟨c,r.val⟩ : Σ c, Fin (n c)) = ⟨c,s.val⟩ :=
          positions.symm.injective (congrArg Subtype.val hrs)
        exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      · intro t
        obtain ⟨⟨c',r⟩, hr⟩ := positions.symm.surjective t.val
        have hc : c' = c := (hcell c' r).symm.trans
          (by rw [hr]; exact t.property.1)
        subst c'
        refine ⟨⟨r, ?_⟩, Subtype.ext hr⟩
        exact (htag c r).trans (by simpa only [hr] using t.property.2)
    simpa only [Fintype.card_subtype] using (Fintype.card_of_bijective hf).symm
  have hg : Graded component shape j i (label q 3 N w) ↔
      ∀ c r, (cwFourthPairGrade q (v c r).down).val = shape c i := by
    constructor
    · intro h c r
      simpa only [hcell] using (hgrade c r).trans (h (positions.symm ⟨c,r⟩))
    · intro h t
      obtain ⟨⟨c,r⟩, rfl⟩ := positions.symm.surjective t
      rw [hcell]
      exact (hgrade c r).symm.trans (h c r)
  have hp : Profile component fourthLeftTag mu j 2 (label q 3 N w) ↔
      ∀ c a, (Finset.univ.filter (fun r : Fin (n c) ↦
        cwSquarePairGrade q (v c r).down.1 = a)).card = counts c a := by
    simp only [Profile, hcard, hmu]
  rw [hg, hp]
  constructor
  · rintro ⟨hg,hp⟩ c
    exact ⟨hg c, fun hi ↦ hp hi c⟩
  · intro h
    exact ⟨fun c ↦ (h c).1, fun hi c ↦ (h c).2 hi⟩

end MME.DWZConcreteRouter

namespace MME.DWZStandardProductRepairAtomic

/-- Concrete atomic CW normalization, preserving the precise projected Z basis.
The pulled-back base predicate is subsequently identified with the literal
coarse/profile predicate using the coordinate router and fiber count identities. -/
theorem atomic_product_normalization
    {K : Type u} [Field K] (q : ℕ) {N k : ℕ}
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (positions : Fin N ≃ Σ c, Fin ((p c).length (m c))) :
    let n := fun c ↦ (p c).length (m c)
    let W := (CWObj K q).kronPow (N * 4)
    let C := fun c ↦ cwFourthConstituent K q (I c) (J c) (L c)
    let b := fun c ↦ constituentBasis K q (I c) (J c) (L c)
    let grade := fun c (a : LiftedCoarseCoordinate.{u} q (L c)) ↦
      cwSquarePairGrade q a.down.val.1
    let S := fun c ↦ prescribedZPower (C c) (b c 2) (grade c) (p c) (m c)
    let H := fun c ↦ ((C c).kronPow (n c)).basisZAllowedGrading
      (kronPowModeBasis (C c) 2 (b c 2) (n c))
      (prescribedZWord (grade c) (p c) (m c))
    let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
    ∃ e : (Fin (N * 4) → ULift.{u} (Fin (q+2))) ≃
        (∀ c, Fin (n c) → ULift.{u} (Coordinate q)),
      (∀ w c r, let t := positions.symm ⟨c,r⟩
        (e w c r).down =
          (((w (finProdFinEquiv (t,0))).down, (w (finProdFinEquiv (t,1))).down),
           ((w (finProdFinEquiv (t,2))).down, (w (finProdFinEquiv (t,3))).down))) ∧
      ∃ β : ∀ c, Basis
        {w : PowIndex (LiftedCoarseCoordinate.{u} q (L c)) (n c) //
          prescribedZWord (grade c) (p c) (m c) w} K ((H c).classOf 2 0),
        (∀ c w, (β c w : ((C c).kronPow (n c)).V 2) =
          kronPowModeBasis (C c) 2 (b c 2) (n c) w.val) ∧
        let base := fun i w ↦ ∀ c,
          (∀ r, cwFourthPairGrade q (e w c r).down = cwFourthBlockType (I c) (J c) (L c) i) ∧
          (i = 2 → ∀ a : Fin 5,
            (Finset.univ.filter (fun r : Fin (n c) ↦
              cwSquarePairGrade q (e w c r).down.1 = a)).card = (p c).count a * m c)
        let G := W.basisAllAllowedGrading B base
        ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin k S).V i,
          PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
            (W.basisAllAllowedSubtensor B base).t = (kronFin k S).t ∧
          ∀ (w : ∀ c, Fin (n c) → LiftedCoarseCoordinate.{u} q (L c))
            (hw : ∀ c, prescribedZWord (grade c) (p c) (m c)
              (PowIndex.ofFun (n c) (w c))),
            F 2 (G.blockProj 2 0 (B 2 (e.symm (fun c r ↦ ⟨(w c r).down.val⟩)))) =
              kronFinModePiBasis k S 2 β
                (fun c ↦ ⟨PowIndex.ofFun (n c) (w c), hw c⟩) := by
  classical
  dsimp only
  let n := fun c ↦ (p c).length (m c)
  let W := (CWObj K q).kronPow (N * 4)
  let X := fun c : Fin k ↦ (cwFourthObj K q).kronPow (n c)
  let U := kronFin k X
  let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
    ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
  let D := fun i ↦ kronFinModePiBasis k X i (fun c ↦
    kronPowModeWordBasis (cwFourthObj K q) i
      ((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm) (n c))
  let P := fun i (w : ∀ c, Fin (n c) → ULift.{u} (Coordinate q)) ↦ ∀ c,
    (∀ r, cwFourthPairGrade q (w c r).down = cwFourthBlockType (I c) (J c) (L c) i) ∧
    (i = 2 → ∀ a : Fin 5,
      (Finset.univ.filter (fun r : Fin (n c) ↦
        cwSquarePairGrade q (w c r).down.1 = a)).card = (p c).count a * m c)
  obtain ⟨e, he, Φ, hΦ, hΦB, _, _, _⟩ :=
    mme_CW_atomic_fourth_component_grouping_projection_transport (K := K) q n positions
  obtain ⟨β, hβ, F1, hF1, hF1B⟩ :=
    mme_CW_fourth_component_profile_projection_normalization (K := K) q I J L p m
  let base := fun i w ↦ P i (e w)
  obtain ⟨F0, hF0, hF0B, _⟩ :=
    mme_basisAllAllowedSubtensor_basis_equiv_transport W U B D Φ (fun _ ↦ e)
      hΦB hΦ base P (fun _ _ ↦ Iff.rfl)
  refine ⟨e, he, (fun c ↦ β c 2), (fun c w ↦ hβ c 2 w),
    (fun i ↦ (F0 i).trans (F1 i)), ?_, ?_⟩
  · change PiTensorProduct.map
      (fun i ↦ (F1 i).toLinearMap.comp (F0 i).toLinearMap) _ = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hF0]
    exact hF1
  · intro w hw
    change F1 2 (F0 2 _) = _
    rw [hF0B]
    simp only [e.apply_symm_apply]
    exact hF1B 2 w hw

/-- The concrete coarse/profile source, with an actual coordinate router and
left-grade covariance. Component labels include their profile and orientation;
the prescribed positions equivalence is supplied for this exact owner. -/
theorem actual_base_normalization
    {K : Type u} [Field K] (q : ℕ) {N k R : ℕ}
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (j : Fin R)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (positions : Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ c r, component j (positions.symm ⟨c,r⟩) = c) :
    let n := fun c ↦ (p c).length (m c)
    let W := (CWObj K q).kronPow (N * 4)
    let C := fun c ↦ cwFourthConstituent K q (I c) (J c) (L c)
    let b := fun c ↦ constituentBasis K q (I c) (J c) (L c)
    let grade := fun c (a : LiftedCoarseCoordinate.{u} q (L c)) ↦
      cwSquarePairGrade q a.down.val.1
    let S := fun c ↦ prescribedZPower (C c) (b c 2) (grade c) (p c) (m c)
    let H := fun c ↦ ((C c).kronPow (n c)).basisZAllowedGrading
      (kronPowModeBasis (C c) 2 (b c 2) (n c))
      (prescribedZWord (grade c) (p c) (m c))
    let Coord := fun c ↦ {w : PowIndex (LiftedCoarseCoordinate.{u} q (L c)) (n c) //
      prescribedZWord (grade c) (p c) (m c) w}
    let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
    let base := fun i w ↦ Graded component shape j i (label q 3 N w) ∧
      (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w))
    let G := W.basisAllAllowedGrading B base
    ∃ β : ∀ c, Basis (Coord c) K ((H c).classOf 2 0),
      (∀ c w, (β c w : ((C c).kronPow (n c)).V 2) =
        kronPowModeBasis (C c) 2 (b c 2) (n c) w.val) ∧
      ∃ route : {w : WordIndex.{u} q 3 N // base 2 w} → (∀ c, Coord c),
      ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin k S).V i,
        PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (W.basisAllAllowedSubtensor B base).t = (kronFin k S).t ∧
        (∀ w, F 2 (G.blockProj 2 0 (B 2 w.val)) = kronFinModePiBasis k S 2 β (route w)) ∧
        ∀ w c r, grade c (PowIndex.get (n c) (route w c).val r) =
          fourthLeftTag (label q 3 N w.val (positions.symm ⟨c,r⟩)) := by
  classical
  dsimp only
  let n := fun c ↦ (p c).length (m c)
  let W := (CWObj K q).kronPow (N * 4)
  let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
    ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
  let grade := fun c (a : LiftedCoarseCoordinate.{u} q (L c)) ↦
    cwSquarePairGrade q a.down.val.1
  let base := fun i w ↦ Graded component shape j i (label q 3 N w) ∧
    (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w))
  obtain ⟨e, he, β, hβ, F, hF, hFB⟩ :=
    atomic_product_normalization (K := K) q I J L p m positions
  let grouped := fun i w ↦ ∀ c,
    (∀ r, cwFourthPairGrade q (e w c r).down = cwFourthBlockType (I c) (J c) (L c) i) ∧
    (i = 2 → ∀ a : Fin 5,
      (Finset.univ.filter (fun r : Fin (n c) ↦
        cwSquarePairGrade q (e w c r).down.1 = a)).card = (p c).count a * m c)
  have hiff (i : Fin 3) (w : WordIndex.{u} q 3 N) : base i w ↔ grouped i w := by
    have h := MME.DWZConcreteRouter.grouped_base_iff component shape mu j i n
      (fun c a ↦ (p c).count a * m c) hmu positions hcell w (e w) (he w)
    apply h.trans
    apply forall_congr'
    intro c
    apply and_congr _ Iff.rfl
    apply forall_congr'
    intro r
    rw [hshape]
    exact Fin.ext_iff.symm
  obtain ⟨A, hA, hAB, _⟩ := mme_basisAllAllowedSubtensor_basis_equiv_transport W W B B
    (fun _ ↦ LinearEquiv.refl K _) (fun _ ↦ Equiv.refl _)
    (fun _ _ ↦ rfl)
    (by change PiTensorProduct.map (fun _ ↦ LinearMap.id) W.t = W.t
        simp only [PiTensorProduct.map_id, LinearMap.id_apply]) base grouped hiff
  let v (w : {w : WordIndex.{u} q 3 N // base 2 w}) (c : Fin k) (r : Fin (n c)) :
      LiftedCoarseCoordinate.{u} q (L c) :=
    ⟨⟨(e w.val c r).down, ((hiff 2 w.val).mp w.property c).1 r⟩⟩
  have hv (w : {w : WordIndex.{u} q 3 N // base 2 w}) (c : Fin k) :
      prescribedZWord (grade c) (p c) (m c) (PowIndex.ofFun (n c) (v w c)) := by
    intro a
    change (Finset.univ.filter (fun r : Fin (n c) ↦
      grade c (PowIndex.get (n c) (PowIndex.ofFun (n c) (v w c)) r) = a)).card = _
    rw [PowIndex.get_ofFun]
    exact ((hiff 2 w.val).mp w.property c).2 rfl a
  let route (w : {w : WordIndex.{u} q 3 N // base 2 w}) :=
    fun c ↦ (⟨PowIndex.ofFun (n c) (v w c), hv w c⟩ :
      {w : PowIndex (LiftedCoarseCoordinate.{u} q (L c)) (n c) //
        prescribedZWord (grade c) (p c) (m c) w})
  refine ⟨β, hβ, route, (fun i ↦ (A i).trans (F i)), ?_, ?_, ?_⟩
  · change PiTensorProduct.map
      (fun i ↦ (F i).toLinearMap.comp (A i).toLinearMap) _ = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hA, hF]
  · intro w
    change F 2 (A 2 _) = _
    rw [hAB]
    have hb := hFB (v w) (hv w)
    have heq : e.symm (fun c r ↦ ⟨(v w c r).down.val⟩) = w.val := by
      change e.symm (e w.val) = w.val
      exact e.symm_apply_apply w.val
    rw [heq] at hb
    exact hb
  · intro w c r
    change grade c (PowIndex.get (n c) (PowIndex.ofFun (n c) (v w c)) r) = _
    rw [PowIndex.get_ofFun]
    change cwSquarePairGrade q (e w.val c r).down.1 = _
    rw [he]
    apply Fin.ext
    rfl

/-- Concrete finite CW extraction-to-standard-product repair. All tensor maps
and shuffles are constructed; only explicit extraction, mask covariance, and
finite combinatorial budgets remain as inputs. -/
theorem actual_CW_standard_product_repair
    {K : Type u} [Field K] (q : ℕ) {N k R : ℕ} (hN : 0 < N)
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (positions : Fin R → Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ j c r, component j ((positions j).symm ⟨c,r⟩) = c) :
    let n := fun c ↦ (p c).length (m c)
    let W := (CWObj K q).kronPow (N * 4)
    let C := fun c ↦ cwFourthConstituent K q (I c) (J c) (L c)
    let b := fun c ↦ constituentBasis K q (I c) (J c) (L c)
    let grade := fun c (a : LiftedCoarseCoordinate.{u} q (L c)) ↦
      cwSquarePairGrade q a.down.val.1
    let S := fun c ↦ prescribedZPower (C c) (b c 2) (grade c) (p c) (m c)
    let Coord := fun c ↦ {w : PowIndex (LiftedCoarseCoordinate.{u} q (L c)) (n c) //
      prescribedZWord (grade c) (p c) (m c) w}
    let Block := (c : Fin k) → {w : PowIndex (Fin 5) (n c) //
      prescribedZWord id (p c) (m c) w}
    let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
    let allowed := fun j i w ↦
      Graded component shape j i (label q 3 N w) ∧
      (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w)) ∧
      (i = 2 → ∀ j', ZCompatible component shape fourthLeftTag mu j'
        (label q 3 N w) → j' = j)
    Nonempty (∀ c, Coord c) →
    Fintype.card Block ≤ 2 ^ (N * 3) →
    ∀ copies : Fin R → MME.DWZSquare.BrokenBlockCopy Block,
      (((N * 3 + 1 : ℕ) : ℝ) ≤ ∑ j, MME.DWZSquare.nonholeFraction (copies j)) →
      (∀ j (w : WordIndex.{u} q 3 N) (z : Block),
        Graded component shape j 2 (label q 3 N w) →
        (∀ c r, PowIndex.get (n c) (z c).val r =
          fourthLeftTag (label q 3 N w ((positions j).symm ⟨c,r⟩))) →
        ((∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N w) → j' = j) ↔ z ∈ (copies j).nonholes)) →
      TensorObj.Restrict (TensorObj.bigAdd (fun j ↦ W.basisAllAllowedSubtensor B (allowed j))) W →
      TensorObj.Restrict (kronFin k S) W := by
  classical
  dsimp only
  let n := fun c ↦ (p c).length (m c)
  let W := (CWObj K q).kronPow (N * 4)
  let C := fun c ↦ cwFourthConstituent K q (I c) (J c) (L c)
  let b := fun c ↦ constituentBasis K q (I c) (J c) (L c)
  let grade := fun c (a : LiftedCoarseCoordinate.{u} q (L c)) ↦
    cwSquarePairGrade q a.down.val.1
  let S := fun c ↦ prescribedZPower (C c) (b c 2) (grade c) (p c) (m c)
  let P := kronFin k S
  let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
    ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
  let base := fun j i w ↦ Graded component shape j i (label q 3 N w) ∧
    (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w))
  let allowed := fun j i w ↦
    Graded component shape j i (label q 3 N w) ∧
    (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w)) ∧
    (i = 2 → ∀ j', ZCompatible component shape fourthLeftTag mu j'
      (label q 3 N w) → j' = j)
  intro hcoord hcard copies hmass hmask hextract
  obtain ⟨factorBasis, labelBlock, system, hBasis, hlabel, _, _, hshuffle⟩ :=
    mme_dwz_prescribed_Z_product_uniform_basis_shuffle k C b (fun _ ↦ 5) grade p m
  let PB := kronFinModePiBasis k S 2 factorBasis
  letI : Nonempty ((c : Fin k) → {w : PowIndex (Fin 5) (n c) //
      prescribedZWord id (p c) (m c) w}) := ⟨labelBlock (Classical.choice hcoord)⟩
  choose SF perm hSF _ hSFB hcov using hshuffle
  obtain ⟨_, _, _, _, _, _, _, hrepair⟩ :=
    mme_dwz_generic_basis_label_hole_cover_tensor_repair P PB labelBlock system
      (fun g i ↦ (SF g i).toLinearMap) perm hSFB hcov hSF N 3 R hN (by decide)
      copies hcard hmass
  have hnorm (j : Fin R) := actual_base_normalization (K := K) q I J L p m
    component shape mu j hshape hmu (positions j) (hcell j)
  choose β hβ route F hF hFB htag using hnorm
  have hβeq (j : Fin R) : β j = factorBasis := by
    funext c
    apply DFunLike.ext
    intro w
    apply Subtype.ext
    exact (hβ j c w).trans (hBasis c w).symm
  have hrouteLabel (j : Fin R) (w : {w : WordIndex.{u} q 3 N // base j 2 w})
      (c : Fin k) (r : Fin (n c)) :
      PowIndex.get (n c) (labelBlock (route j w) c).val r =
        fourthLeftTag (label q 3 N w.val ((positions j).symm ⟨c,r⟩)) := by
    rw [hlabel]
    rw [PowIndex.get_ofFun]
    exact htag j w c r
  have hXY (j : Fin R) (i : Fin 3) (hi : i ≠ 2) (w) :
      allowed j i w ↔ base j i w := by simp [allowed, base, hi]
  have hmask' (j : Fin R) (w : WordIndex.{u} q 3 N) :
      allowed j 2 w ↔ ∃ ha : base j 2 w,
        labelBlock (route j ⟨w, ha⟩) ∈ (copies j).nonholes := by
    constructor
    · intro hw
      have ha : base j 2 w := ⟨hw.1, hw.2.1⟩
      exact ⟨ha, (hmask j w _ hw.1 (hrouteLabel j ⟨w, ha⟩)).mp (hw.2.2 rfl)⟩
    · rintro ⟨ha, hh⟩
      refine ⟨ha.1, ha.2, fun _ ↦ ?_⟩
      exact (hmask j w _ ha.1 (hrouteLabel j ⟨w, ha⟩)).mpr hh
  have hbroken (j : Fin R) :=
    MME.DWZStandardProductRepairComposition.projected_owner_normalizes_to_literal
      W P B PB labelBlock (copies j).nonholes (base j) (allowed j) (route j)
      (fun i ↦ (F j i).toLinearMap) (hF j)
      (fun w hw ↦ by
        have h := hFB j ⟨w, hw⟩
        rw [hβeq j] at h
        exact h)
      (hXY j) (hmask' j)
  exact hrepair.trans ((mme_bigAdd_mono_restrict hbroken).trans hextract)

end MME.DWZStandardProductRepairAtomic

theorem solution
    {K : Type u} [Field K] (q : ℕ) {N k R : ℕ} (hN : 0 < N)
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (positions : Fin R → Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ j c r, component j ((positions j).symm ⟨c,r⟩) = c) :
    let n := fun c ↦ (p c).length (m c)
    let W := (CWObj K q).kronPow (N * 4)
    let C := fun c ↦ cwFourthConstituent K q (I c) (J c) (L c)
    let b := fun c ↦ constituentBasis K q (I c) (J c) (L c)
    let grade := fun c (a : LiftedCoarseCoordinate.{u} q (L c)) ↦
      cwSquarePairGrade q a.down.val.1
    let S := fun c ↦ prescribedZPower (C c) (b c 2) (grade c) (p c) (m c)
    let Coord := fun c ↦ {w : PowIndex (LiftedCoarseCoordinate.{u} q (L c)) (n c) //
      prescribedZWord (grade c) (p c) (m c) w}
    let Block := (c : Fin k) → {w : PowIndex (Fin 5) (n c) //
      prescribedZWord id (p c) (m c) w}
    let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
    let allowed := fun j i w ↦
      Graded component shape j i (label q 3 N w) ∧
      (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w)) ∧
      (i = 2 → ∀ j', ZCompatible component shape fourthLeftTag mu j'
        (label q 3 N w) → j' = j)
    Nonempty (∀ c, Coord c) →
    Fintype.card Block ≤ 2 ^ (N * 3) →
    ∀ copies : Fin R → MME.DWZSquare.BrokenBlockCopy Block,
      (((N * 3 + 1 : ℕ) : ℝ) ≤ ∑ j, MME.DWZSquare.nonholeFraction (copies j)) →
      (∀ j (w : WordIndex.{u} q 3 N) (z : Block),
        Graded component shape j 2 (label q 3 N w) →
        (∀ c r, PowIndex.get (n c) (z c).val r =
          fourthLeftTag (label q 3 N w ((positions j).symm ⟨c,r⟩))) →
        ((∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N w) → j' = j) ↔ z ∈ (copies j).nonholes)) →
      TensorObj.Restrict (TensorObj.bigAdd (fun j ↦ W.basisAllAllowedSubtensor B (allowed j))) W →
      TensorObj.Restrict (kronFin k S) W := by
  exact MME.DWZStandardProductRepairAtomic.actual_CW_standard_product_repair
    q hN I J L p m component shape mu hshape hmu positions hcell
