-- Prove2me | solution 1 for mme_dwz_canonical022_prescribed_z_MM_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T06:41:17.831332+00:00
-- url     : https://prove2.me/submissions/daee7b70-14e0-420f-a950-c2243076e12d

import Theorems.Thm_mme_dwz_cw_square_central_022_all_word_power_router
import Theorems.Thm_mme_dwz_central_022_202_power_word_coordinates
import Theorems.Thm_mme_little_endian_MM_kronPow_tensor
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Definitions.Def_mme_dwz_central_restricted_word_projectors
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

open MME MME.DWZFineChannel MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped Classical

universe u v

set_option autoImplicit false
set_option warningAsError true

private theorem fine022SourcePair_covers (q : ℕ) (p : CoarsePair q 2) :
    ∃ c : Fine022Channel q, fine022SourcePair q c 2 = p.1 := by
  rcases p with ⟨⟨a, b⟩, hp⟩
  have hgrade : (cwSquareCoordGrade q a).val + (cwSquareCoordGrade q b).val = 2 :=
    congrArg Fin.val hp
  by_cases ha0 : a.val = 0
  · have hbT : b.val = q + 1 := by
      simp only [cwSquareCoordGrade, ha0, ↓reduceIte] at hgrade
      split_ifs at hgrade <;> simp_all
    refine ⟨Sum.inr (Sum.inr 0), ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact ha0.symm
    · exact hbT.symm
  by_cases haT : a.val = q + 1
  · have hb0 : b.val = 0 := by
      simp only [cwSquareCoordGrade, haT, ↓reduceIte] at hgrade
      split_ifs at hgrade <;> simp_all
    refine ⟨Sum.inl 0, ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact haT.symm
    · exact hb0.symm
  have hb0 : b.val ≠ 0 := by
    intro hb
    simp [cwSquareCoordGrade, ha0, haT, hb] at hgrade
  have hbT : b.val ≠ q + 1 := by
    intro hb
    simp [cwSquareCoordGrade, ha0, haT, hb] at hgrade
  have ha : a.val - 1 < q := by omega
  have hb : b.val - 1 < q := by omega
  refine ⟨Sum.inr (Sum.inl (⟨a.val - 1, ha⟩, ⟨b.val - 1, hb⟩)), ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change a.val - 1 + 1 = a.val
    omega
  · change b.val - 1 + 1 = b.val
    omega

private noncomputable def decode022 (q : ℕ) (p : CoarsePair q 2) : Fine022Channel q :=
  Classical.choose (fine022SourcePair_covers q p)

private theorem decode022_pair (q : ℕ) (p : CoarsePair q 2) :
    fine022SourcePair q (decode022 q p) 2 = p.1 :=
  Classical.choose_spec (fine022SourcePair_covers q p)

private theorem decode022_injective (q : ℕ) : Function.Injective (decode022 q) := by
  intro p p' h
  apply Subtype.ext
  rw [← decode022_pair q p, ← decode022_pair q p', h]

private theorem basis_submodule_cast_apply_coe
    {K V : Type u} {I : Type v} [Field K] [AddCommGroup V] [Module K V]
    {P Q : Submodule K V} (h : P = Q) (b : Basis I K P) (i : I) :
    ((cast (congrArg (fun R : Submodule K V ↦ Basis I K R) h) b) i : V) =
      (b i : V) := by
  subst Q
  rfl

private theorem coarseClassBasis_val
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (c : Fin 5)
    (p : CoarsePair q c) :
    (coarseClassBasis (K := K) q i c p).1 =
      cwSquareCanonicalBasis K q i p.1 := by
  let b := cwSquareCanonicalBasis K q i
  let v : CoarsePair q c →
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) := fun p ↦ b p.1
  have hv : LinearIndependent K v := by
    simpa [v, Function.comp_def] using
      b.linearIndependent.comp (fun p : CoarsePair q c ↦ p.1)
        Subtype.val_injective
  have hset : Set.range v = b '' {p | cwSquarePairGrade q p = c} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hsub :
      cwBasisGrade (cwSquareCanonicalBasis K q i) (cwSquarePairGrade q) c =
        Submodule.span K (Set.range v) := by
    unfold cwBasisGrade
    simpa only [b] using congrArg (Submodule.span K) hset.symm
  unfold coarseClassBasis
  dsimp only
  change ((((Eq.mpr
      (congrArg
        (fun R : Submodule K
            ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) ↦
          Basis (CoarsePair q c) K R) hsub)
      (Basis.span hv)) :
      Basis (CoarsePair q c) K
        (cwBasisGrade (cwSquareCanonicalBasis K q i)
          (cwSquarePairGrade q) c)) p).1) = _
  simpa only [Basis.span_apply, b, v] using
    basis_submodule_cast_apply_coe hsub.symm (Basis.span hv) p

private noncomputable def canonical022ZBasis (K : Type u) [Field K] (q : ℕ) :
    Basis (LiftedCoarsePair.{u} q 2) K ((Central022Block K q).V 2) :=
  (coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm

private theorem canonical022ZBasis_eq_source
    (K : Type u) [Field K] (q : ℕ) (p : LiftedCoarsePair.{u} q 2) :
    canonical022ZBasis K q p = central022SourceVec K q (decode022 q p.down) 2 := by
  apply Subtype.ext
  unfold central022SourceVec
  rw [TensorObj.TypeGrading.blockProj_apply_mem]
  · change (((coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm) p).1 = _
    rw [Basis.reindex_apply]
    change (coarseClassBasis (K := K) q 2 2 p.down).1 =
      cwSquareCanonicalBasis K q 2 (fine022SourcePair q (decode022 q p.down) 2)
    rw [coarseClassBasis_val, decode022_pair]
  · rw [decode022_pair]
    exact Submodule.subset_span ⟨p.down.1, p.down.2, rfl⟩

private theorem canonical022SourceWord_eq_basis
    (K : Type u) [Field K] (q : ℕ) :
    ∀ (n : ℕ) (w : PowIndex (LiftedCoarsePair.{u} q 2) n),
      central022SourceWordVec K q n
          (fun r ↦ decode022 q (PowIndex.get n w r).down) 2 =
        kronPowModeBasis (Central022Block K q) 2 (canonical022ZBasis K q) n w
  | 0, w => by
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      change (1 : K) =
        (Basis.singleton (PowIndex (LiftedCoarsePair.{u} q 2) 0) K) PUnit.unit
      exact (Basis.singleton_apply _ _ _).symm
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      change central022SourceVec K q (decode022 q a.down) 2 ⊗ₜ[K]
          central022SourceWordVec K q n
            (fun r ↦ decode022 q (PowIndex.get n tail r).down) 2 =
        (Module.Basis.tensorProduct (canonical022ZBasis K q)
          (kronPowModeBasis (Central022Block K q) 2
            (canonical022ZBasis K q) n)) (a, tail)
      rw [Module.Basis.tensorProduct_apply, canonical022ZBasis_eq_source,
        canonical022SourceWord_eq_basis K q n tail]

private noncomputable def wordCoordinate (q n : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} q 2) n) : Fin ((q ^ 2 + 2) ^ n) :=
  fineChannelWordIndex q n (fun r ↦ decode022 q (PowIndex.get n w r).down)

private theorem wordCoordinate_injective (q n : ℕ) :
    Function.Injective (wordCoordinate.{u} q n) := by
  intro w v h
  have hdecoded := (fineChannelWordIndex q n).injective h
  apply (PowIndex.equivFun (LiftedCoarsePair.{u} q 2) n).injective
  funext r
  apply ULift.ext
  exact decode022_injective q (congrFun hdecoded r)

private theorem projector_Z_outside
    {K : Type u} [Field K] {q n D : ℕ}
    (e : Fin D ↪ Fin ((q ^ 2 + 2) ^ n)) (k' : Fin ((q ^ 2 + 2) ^ n))
    (hout : ∀ k, e k ≠ k') :
    central022RestrictedProjector (K := K) e 2
      (central022FlatMMVec K q n k' 2) = 0 := by
  change (LinearMap.funLeft K K
      (fun ab : Fin D × Fin 1 ↦ (e ab.1, unitWordIndex n)))
      (Pi.single (k', unitWordIndex n) 1) = 0
  funext ab
  simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply]
  have hne : (e ab.1, unitWordIndex n) ≠ (k', unitWordIndex n) := by
    intro h
    exact hout ab.1 (congrArg Prod.fst h)
  simp [hne]

private theorem canonical022_allowed_restrict
    (K : Type u) [Field K] (q n : ℕ)
    (allowed : PowIndex (LiftedCoarsePair.{u} q 2) n → Prop) :
    TensorObj.Restrict (MMObj K 1 1 (Nat.card {w // allowed w}))
      (((Central022Block K q).kronPow n).basisZAllowedSubtensor
        (kronPowModeBasis (Central022Block K q) 2 (canonical022ZBasis K q) n)
        allowed) := by
  classical
  let W := {w : PowIndex (LiftedCoarsePair.{u} q 2) n // allowed w}
  let D := Nat.card W
  let index : W ≃ Fin D :=
    (Fintype.equivFin W).trans (finCongr Nat.card_eq_fintype_card.symm)
  let e : Fin D ↪ Fin ((q ^ 2 + 2) ^ n) :=
    ⟨fun k ↦ wordCoordinate q n (index.symm k).1, by
      intro k l h
      apply index.symm.injective
      apply Subtype.ext
      exact wordCoordinate_injective q n h⟩
  have outside (w : PowIndex (LiftedCoarsePair.{u} q 2) n) (hw : ¬ allowed w) :
      ∀ k, e k ≠ wordCoordinate q n w := by
    intro k hk
    apply hw
    have heq : (index.symm k).1 = w := wordCoordinate_injective q n hk
    exact heq ▸ (index.symm k).2
  obtain ⟨source, htensor, hword⟩ :=
    mme_dwz_cw_square_central_022_all_word_power_router K q n
  obtain ⟨hcoordinate, _⟩ := mme_dwz_central_022_202_power_word_coordinates K q n
  let f : ∀ i, ((Central022Block K q).kronPow n).V i →ₗ[K]
      (MMObj K 1 1 D).V i := fun i ↦
    (central022RestrictedProjector (K := K) e i).comp
      ((littleEndianPowerMaps K 1 1 (q ^ 2 + 2) n i).comp (source i))
  have hmap : PiTensorProduct.map f ((Central022Block K q).kronPow n).t =
      (MMObj K 1 1 D).t := by
    change PiTensorProduct.map
      (fun i ↦ (central022RestrictedProjector (K := K) e i) ∘ₗ
        ((littleEndianPowerMaps K 1 1 (q ^ 2 + 2) n i) ∘ₗ source i))
        ((Central022Block K q).kronPow n).t = _
    rw [PiTensorProduct.map_comp, PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [htensor, mme_little_endian_MM_kronPow_tensor,
      central022RestrictedProjector_maps_tensor]
  have hvanish : ∀ w, ¬ allowed w → f 2
      (kronPowModeBasis (Central022Block K q) 2 (canonical022ZBasis K q) n w) = 0 := by
    intro w hw
    simp only [f, LinearMap.comp_apply]
    rw [← canonical022SourceWord_eq_basis K q n w,
      hword (fun r ↦ decode022 q (PowIndex.get n w r).down) 2,
      hcoordinate (fun r ↦ decode022 q (PowIndex.get n w r).down) 2]
    exact projector_Z_outside e (wordCoordinate q n w) (outside w hw)
  exact mme_restrict_basisZAllowedSubtensor_of_vanishes
    ((Central022Block K q).kronPow n) (MMObj K 1 1 D)
    (kronPowModeBasis (Central022Block K q) 2 (canonical022ZBasis K q) n)
    allowed f hmap hvanish

theorem solution
    (K : Type u) [Field K] (q : ℕ) (p : IntegerZSplitProfile 3) (m : ℕ) :
    let bZ : Basis (LiftedCoarsePair.{u} q 2) K ((Central022Block K q).V 2) :=
      (coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm
    let D := Nat.card {w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w}
    TensorObj.Restrict (MMObj K 1 1 D)
      (prescribedZPower (Central022Block K q) bZ LiftedCoarsePair.leftGrade p m) := by
  classical
  exact canonical022_allowed_restrict K q (p.length m)
    (prescribedZWord LiftedCoarsePair.leftGrade p m)
