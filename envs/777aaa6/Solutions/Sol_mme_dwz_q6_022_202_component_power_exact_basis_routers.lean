-- Prove2me | solution 1 for mme_dwz_q6_022_202_component_power_exact_basis_routers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:40:17.774972+00:00
-- url     : https://prove2.me/submissions/820253a4-7a2a-4039-a5eb-739a0fadda65

import Mathlib.Tactic
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_central_restricted_word_projectors
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_dwz_cw_square_central_022_202_source_router
import Theorems.Thm_mme_dwz_cw_square_central_022_all_word_power_router
import Theorems.Thm_mme_dwz_cw_square_central_202_all_word_power_router
import Theorems.Thm_mme_little_endian_MM_kronPow_tensor
import Theorems.Thm_mme_dwz_central_022_202_power_word_coordinates
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val

open PiTensorProduct TensorProduct Module
open MME MME.DWZFineChannel MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace MME.DWZCentral022RestrictedBridge

theorem fine022SourcePair_grade_two
    (c : Fine022Channel 6) :
    cwSquarePairGrade 6 (fine022SourcePair 6 c 2) = 2 := by
  rcases c with c | c
  · fin_cases c
    decide
  · rcases c with ij | c
    · rcases ij with ⟨i, j⟩
      have hiT : i.val + 1 ≠ 7 := by omega
      have hjT : j.val + 1 ≠ 7 := by omega
      simp [fine022SourcePair, cwSquarePairGrade, cwSquareCoordGrade,
        cwM, hiT, hjT]
    · fin_cases c
      decide

def fine022CoarsePair (c : Fine022Channel 6) : CoarsePair 6 2 :=
  ⟨fine022SourcePair 6 c 2, fine022SourcePair_grade_two c⟩

def coarsePairFine022 (p : CoarsePair 6 2) : Fine022Channel 6 :=
  if p.1.1.val = 7 then
    Sum.inl 0
  else if p.1.1.val = 0 then
    Sum.inr (Sum.inr 0)
  else
    Sum.inr (Sum.inl
      (Fin.ofNat 6 (p.1.1.val - 1), Fin.ofNat 6 (p.1.2.val - 1)))

theorem coarsePairFine022_left_inverse :
    Function.LeftInverse coarsePairFine022 fine022CoarsePair := by
  intro c
  rcases c with c | c
  · fin_cases c
    rfl
  · rcases c with ij | c
    · rcases ij with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> rfl
    · fin_cases c
      rfl

theorem coarsePairFine022_right_inverse :
    Function.RightInverse coarsePairFine022 fine022CoarsePair := by
  rintro ⟨⟨a, b⟩, hp⟩
  apply Subtype.ext
  fin_cases a <;> fin_cases b <;>
    simp [coarsePairFine022, fine022CoarsePair, fine022SourcePair,
      cwSquarePairGrade, cwSquareCoordGrade, cwO, cwM, cwT] at hp ⊢

noncomputable def fine022CoarseEquiv :
    Fine022Channel 6 ≃ CoarsePair 6 2 where
  toFun := fine022CoarsePair
  invFun := coarsePairFine022
  left_inv := coarsePairFine022_left_inverse
  right_inv := coarsePairFine022_right_inverse

theorem fine022CoarseEquiv_val (c : Fine022Channel 6) :
    (fine022CoarseEquiv c).1 = fine022SourcePair 6 c 2 := rfl

noncomputable def central022ZBasis
    (K : Type u) [Field K] :
    Basis (LiftedCoarsePair.{u} 6 2) K ((Central022Block K 6).V 2) :=
  (coarseClassBasis (K := K) 6 2 2).reindex Equiv.ulift.symm

theorem central022ZBasis_blockProj
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 2) :
    central022ZBasis K p =
      (cwSquareCanonicalGrading K 6).blockProj 2 2
        (cwSquareCanonicalBasis K 6 2 p.down.1) := by
  apply Subtype.ext
  rw [TensorObj.TypeGrading.blockProj_apply_mem]
  · have hr :
        central022ZBasis K p =
          coarseClassBasis (K := K) 6 2 2 p.down := by
      exact Module.Basis.reindex_apply
        (coarseClassBasis (K := K) 6 2 2) Equiv.ulift.symm p
    rw [hr]
    exact mme_dwz_coarseClassBasis_q6_val K 2 2 p.down
  · exact Submodule.subset_span ⟨p.down.1, p.down.2, rfl⟩

theorem central022ZBasis_eq_source
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 2) :
    central022ZBasis K p =
      central022SourceVec K 6 (fine022CoarseEquiv.symm p.down) 2 := by
  rw [central022ZBasis_blockProj]
  unfold central022SourceVec
  congr 2
  have h := fine022CoarseEquiv.apply_symm_apply p.down
  exact (congrArg Subtype.val h).symm

theorem central022SourceWordVec_eq_basis
    (K : Type u) [Field K] :
    ∀ (n : ℕ) (w : PowIndex (LiftedCoarsePair.{u} 6 2) n),
      central022SourceWordVec K 6 n
          (fun r ↦ fine022CoarseEquiv.symm (PowIndex.get n w r).down) 2 =
        kronPowModeBasis (Central022Block K 6) 2
          (central022ZBasis K) n w
  | 0, w => by
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      change (1 : K) =
        (Basis.singleton (PowIndex (LiftedCoarsePair.{u} 6 2) 0) K)
          PUnit.unit
      exact (Basis.singleton_apply _ _ _).symm
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      change
        central022SourceVec K 6 (fine022CoarseEquiv.symm a.down) 2 ⊗ₜ[K]
            central022SourceWordVec K 6 n
              (fun r ↦ fine022CoarseEquiv.symm
                (PowIndex.get n tail r).down) 2 =
          (Module.Basis.tensorProduct (central022ZBasis K)
            (kronPowModeBasis (Central022Block K 6) 2
              (central022ZBasis K) n)) (a, tail)
      rw [Module.Basis.tensorProduct_apply]
      rw [central022ZBasis_eq_source]
      rw [central022SourceWordVec_eq_basis K n tail]

theorem row9_componentPowerZBasis_eq_sourceWord
    (K : Type u) [Field K] (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2)
      (MME.DWZTable2Counts.component 9 * m)) :
    componentPowerZBasis K 9 m w =
      central022SourceWordVec K 6
        (MME.DWZTable2Counts.component 9 * m)
        (fun r ↦ fine022CoarseEquiv.symm
          (PowIndex.get (MME.DWZTable2Counts.component 9 * m) w r).down) 2 := by
  change kronPowModeBasis (Central022Block K 6) 2
      (central022ZBasis K)
      (MME.DWZTable2Counts.component 9 * m) w = _
  exact (central022SourceWordVec_eq_basis K
    (MME.DWZTable2Counts.component 9 * m) w).symm

theorem central202ZBasis_eq_source
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 2) :
    central022ZBasis K p =
      central202SourceVec K 6 (fine022CoarseEquiv.symm p.down) 2 := by
  rw [central022ZBasis_blockProj]
  unfold central202SourceVec
  congr 2
  have h := fine022CoarseEquiv.apply_symm_apply p.down
  exact (congrArg Subtype.val h).symm

theorem central202SourceWordVec_eq_basis
    (K : Type u) [Field K] :
    ∀ (n : ℕ) (w : PowIndex (LiftedCoarsePair.{u} 6 2) n),
      central202SourceWordVec K 6 n
          (fun r ↦ fine022CoarseEquiv.symm (PowIndex.get n w r).down) 2 =
        kronPowModeBasis (Central202Block K 6) 2
          (central022ZBasis K) n w
  | 0, w => by
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      change (1 : K) =
        (Basis.singleton (PowIndex (LiftedCoarsePair.{u} 6 2) 0) K)
          PUnit.unit
      exact (Basis.singleton_apply _ _ _).symm
  | n + 1, w => by
      rcases w with ⟨a, tail⟩
      change
        central202SourceVec K 6 (fine022CoarseEquiv.symm a.down) 2 ⊗ₜ[K]
            central202SourceWordVec K 6 n
              (fun r ↦ fine022CoarseEquiv.symm
                (PowIndex.get n tail r).down) 2 =
          (Module.Basis.tensorProduct (central022ZBasis K)
            (kronPowModeBasis (Central202Block K 6) 2
              (central022ZBasis K) n)) (a, tail)
      rw [Module.Basis.tensorProduct_apply]
      rw [central202ZBasis_eq_source]
      rw [central202SourceWordVec_eq_basis K n tail]
      rfl

theorem row10_componentPowerZBasis_eq_sourceWord
    (K : Type u) [Field K] (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2)
      (MME.DWZTable2Counts.component 10 * m)) :
    componentPowerZBasis K 10 m w =
      central202SourceWordVec K 6
        (MME.DWZTable2Counts.component 10 * m)
        (fun r ↦ fine022CoarseEquiv.symm
          (PowIndex.get (MME.DWZTable2Counts.component 10 * m) w r).down) 2 := by
  change kronPowModeBasis (Central202Block K 6) 2
      (central022ZBasis K)
      (MME.DWZTable2Counts.component 10 * m) w = _
  exact (central202SourceWordVec_eq_basis K
    (MME.DWZTable2Counts.component 10 * m) w).symm

end MME.DWZCentral022RestrictedBridge

open MME.DWZCentral022RestrictedBridge

namespace MME.DWZCentral022AllowedExtraction

abbrev row9Length (m : ℕ) : ℕ :=
  MME.DWZTable2Counts.component 9 * m

def row9Allowed (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m)) : Prop :=
  componentWordAllowed 9 m w

def row9AllowedWord (m : ℕ) :=
  {w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m) //
    row9Allowed m w}

noncomputable instance row9AllowedWordFintype (m : ℕ) :
    Fintype (row9AllowedWord.{u} m) := by
  unfold row9AllowedWord
  letI : DecidablePred (row9Allowed m) := Classical.decPred _
  infer_instance

noncomputable def row9DecodedWord (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m)) :
    Fin (row9Length m) → Fine022Channel 6 := fun r ↦
  fine022CoarseEquiv.symm (PowIndex.get (row9Length m) w r).down

noncomputable def row9WordCoordinate (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m)) :
    Fin ((6 ^ 2 + 2) ^ row9Length m) :=
  fineChannelWordIndex 6 (row9Length m) (row9DecodedWord m w)

theorem row9WordCoordinate_injective (m : ℕ) :
    Function.Injective (row9WordCoordinate.{u} m) := by
  intro w v h
  have hdecoded : row9DecodedWord m w = row9DecodedWord m v :=
    (fineChannelWordIndex 6 (row9Length m)).injective h
  apply (PowIndex.equivFun (LiftedCoarsePair.{u} 6 2) (row9Length m)).injective
  funext r
  apply ULift.ext
  exact fine022CoarseEquiv.symm.injective (congrFun hdecoded r)

end MME.DWZCentral022AllowedExtraction

open MME.DWZCentral022RestrictedBridge
open MME.DWZCentral022AllowedExtraction

/-- Exact flat, basis-labelled routers for the two central component powers.
The coordinate embeddings are quantified in the public statement, so no
workspace-private decoding type escapes. -/
theorem solution
    (K : Type u) [Field K] (m : ℕ) :
    (∃ (coord : PowIndex (LiftedCoarsePair.{u} 6 2)
          (MME.DWZTable2Counts.component 9 * m) ↪
            Fin ((6 ^ 2 + 2) ^ (MME.DWZTable2Counts.component 9 * m)))
        (router : ∀ s : Fin 3,
          (((canonicalComponentBlock K (9 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 9 * m)).V s) →ₗ[K]
            (MMObj K
              (1 ^ (MME.DWZTable2Counts.component 9 * m))
              (1 ^ (MME.DWZTable2Counts.component 9 * m))
              ((6 ^ 2 + 2) ^
                (MME.DWZTable2Counts.component 9 * m))).V s),
      PiTensorProduct.map router
          ((canonicalComponentBlock K (9 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 9 * m)).t =
        (MMObj K
          (1 ^ (MME.DWZTable2Counts.component 9 * m))
          (1 ^ (MME.DWZTable2Counts.component 9 * m))
          ((6 ^ 2 + 2) ^
            (MME.DWZTable2Counts.component 9 * m))).t ∧
      ∀ w, router 2 (componentPowerZBasis K (9 : Fin 15) m w) =
        central022FlatMMVec K 6
          (MME.DWZTable2Counts.component 9 * m) (coord w) 2) ∧
    (∃ (coord : PowIndex (LiftedCoarsePair.{u} 6 2)
          (MME.DWZTable2Counts.component 10 * m) ↪
            Fin ((6 ^ 2 + 2) ^ (MME.DWZTable2Counts.component 10 * m)))
        (router : ∀ s : Fin 3,
          (((canonicalComponentBlock K (10 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 10 * m)).V s) →ₗ[K]
            (MMObj K
              ((6 ^ 2 + 2) ^
                (MME.DWZTable2Counts.component 10 * m))
              (1 ^ (MME.DWZTable2Counts.component 10 * m))
              (1 ^ (MME.DWZTable2Counts.component 10 * m))).V s),
      PiTensorProduct.map router
          ((canonicalComponentBlock K (10 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 10 * m)).t =
        (MMObj K
          ((6 ^ 2 + 2) ^
            (MME.DWZTable2Counts.component 10 * m))
          (1 ^ (MME.DWZTable2Counts.component 10 * m))
          (1 ^ (MME.DWZTable2Counts.component 10 * m))).t ∧
      ∀ w, router 2 (componentPowerZBasis K (10 : Fin 15) m w) =
        central202FlatMMVec K 6
          (MME.DWZTable2Counts.component 10 * m) (coord w) 2) := by
  let n := MME.DWZTable2Counts.component 9 * m
  let P := (6 ^ 2 + 2) ^ n
  let coord : PowIndex (LiftedCoarsePair.{u} 6 2) n ↪ Fin P :=
    ⟨row9WordCoordinate m, row9WordCoordinate_injective m⟩
  let n10 := MME.DWZTable2Counts.component 10 * m
  let P10 := (6 ^ 2 + 2) ^ n10
  let coord10 : PowIndex (LiftedCoarsePair.{u} 6 2) n10 ↪ Fin P10 := by
    let decode : PowIndex (LiftedCoarsePair.{u} 6 2) n10 →
        (Fin n10 → Fine202Channel 6) := fun w r ↦
      fine022CoarseEquiv.symm (PowIndex.get n10 w r).down
    refine ⟨fun w ↦ fineChannelWordIndex 6 n10 (decode w), ?_⟩
    intro w v h
    have hdecoded : decode w = decode v :=
      (fineChannelWordIndex 6 n10).injective h
    apply (PowIndex.equivFun (LiftedCoarsePair.{u} 6 2) n10).injective
    funext r
    apply ULift.ext
    exact fine022CoarseEquiv.symm.injective (congrFun hdecoded r)
  rcases mme_dwz_cw_square_central_022_all_word_power_router K 6 n with
    ⟨source022, htensor022, hword022⟩
  rcases mme_dwz_cw_square_central_202_all_word_power_router K 6 n10 with
    ⟨source202, htensor202, hword202⟩
  obtain ⟨hcoordinate022, _⟩ :=
    mme_dwz_central_022_202_power_word_coordinates K 6 n
  obtain ⟨_, hcoordinate202⟩ :=
    mme_dwz_central_022_202_power_word_coordinates K 6 n10
  let raw022 : ∀ s : Fin 3,
      ((Central022Block K 6).kronPow n).V s →ₗ[K]
        (MMObj K (1 ^ n) (1 ^ n) ((6 ^ 2 + 2) ^ n)).V s := fun s ↦
    (littleEndianPowerMaps K 1 1 (6 ^ 2 + 2) n s).comp
      (source022 s)
  let raw202 : ∀ s : Fin 3,
      ((Central202Block K 6).kronPow n10).V s →ₗ[K]
        (MMObj K ((6 ^ 2 + 2) ^ n10) (1 ^ n10) (1 ^ n10)).V s := fun s ↦
    (littleEndianPowerMaps K (6 ^ 2 + 2) 1 1 n10 s).comp
      (source202 s)
  have hraw022 : PiTensorProduct.map raw022
      ((Central022Block K 6).kronPow n).t =
        (MMObj K (1 ^ n) (1 ^ n) ((6 ^ 2 + 2) ^ n)).t := by
    change PiTensorProduct.map
        (fun s ↦ (littleEndianPowerMaps K 1 1 (6 ^ 2 + 2) n s) ∘ₗ
          source022 s) ((Central022Block K 6).kronPow n).t = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [htensor022, mme_little_endian_MM_kronPow_tensor]
  have hraw202 : PiTensorProduct.map raw202
      ((Central202Block K 6).kronPow n10).t =
        (MMObj K ((6 ^ 2 + 2) ^ n10) (1 ^ n10) (1 ^ n10)).t := by
    change PiTensorProduct.map
        (fun s ↦ (littleEndianPowerMaps K (6 ^ 2 + 2) 1 1 n10 s) ∘ₗ
          source202 s) ((Central202Block K 6).kronPow n10).t = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [htensor202, mme_little_endian_MM_kronPow_tensor]
  have hbasis022 : ∀ w,
      raw022 2 (componentPowerZBasis K (9 : Fin 15) m w) =
        central022FlatMMVec K 6 n (coord w) 2 := by
    intro w
    simp only [raw022, LinearMap.comp_apply]
    rw [row9_componentPowerZBasis_eq_sourceWord]
    rw [hword022, hcoordinate022]
    rfl
  have hbasis202 : ∀ w,
      raw202 2 (componentPowerZBasis K (10 : Fin 15) m w) =
        central202FlatMMVec K 6 n10 (coord10 w) 2 := by
    intro w
    simp only [raw202, LinearMap.comp_apply]
    rw [row10_componentPowerZBasis_eq_sourceWord]
    rw [hword202, hcoordinate202]
    rfl
  constructor
  · refine ⟨coord, ?_, ?_, ?_⟩
    · simpa only [n, P, canonicalComponentBlock,
        MME.DWZSquare.shapeX, MME.DWZSquare.shapeY,
        MME.DWZSquare.shapeZ] using raw022
    · simpa only [n, P, canonicalComponentBlock,
        MME.DWZSquare.shapeX, MME.DWZSquare.shapeY,
        MME.DWZSquare.shapeZ] using hraw022
    · simpa only [n, P, canonicalComponentBlock,
        MME.DWZSquare.shapeX, MME.DWZSquare.shapeY,
        MME.DWZSquare.shapeZ] using hbasis022
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [n10, P10] using coord10
    · simpa only [n10, P10,
        canonicalComponentBlock, MME.DWZSquare.shapeX,
        MME.DWZSquare.shapeY, MME.DWZSquare.shapeZ] using raw202
    · simpa only [n10, P10,
        canonicalComponentBlock, MME.DWZSquare.shapeX,
        MME.DWZSquare.shapeY, MME.DWZSquare.shapeZ] using hraw202
    · simpa only [n10, P10,
        canonicalComponentBlock, MME.DWZSquare.shapeX,
        MME.DWZSquare.shapeY, MME.DWZSquare.shapeZ] using hbasis202
