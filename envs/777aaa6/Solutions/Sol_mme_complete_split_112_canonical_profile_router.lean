-- Prove2me | solution 1 for mme_complete_split_112_canonical_profile_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:26:40.468788+00:00
-- url     : https://prove2.me/submissions/fe490b24-0078-474d-b6dc-4b336c1a7af1

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_CW_square_canonical_112_full_basis_router
import Theorems.Thm_mme_complete_split_restrictedPower_basis_router
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate

open MME MME.CompleteSplit112 MME.CompleteSplit MME.DWZComponentRestriction Module
open scoped Classical NNReal

universe u v

set_option autoImplicit false
set_option warningAsError true

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

private theorem canonicalBasis_eq_blockProj
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (p : CanonicalCoord.{u} q s) :
    canonicalBasis K q s p =
      (cwSquareCanonicalGrading K q).blockProj s (cwSquareBlockType 1 1 2 s)
        (cwSquareCanonicalBasis K q s p.down.1) := by
  apply Subtype.ext
  rw [TensorObj.TypeGrading.blockProj_apply_mem]
  · change (((coarseClassBasis (K := K) q s (cwSquareBlockType 1 1 2 s)).reindex
      Equiv.ulift.symm) p).1 = _
    rw [Module.Basis.reindex_apply]
    exact coarseClassBasis_val K q s (cwSquareBlockType 1 1 2 s) p.down
  · exact Submodule.subset_span ⟨p.down.1, p.down.2, rfl⟩

/-- The actual coupled112 complete-profile power restricts from the literal
canonical CW square112 complete-profile power, in all three modes. -/
theorem solution
    (K : Type u) [Field K] (q : ℕ)
    (beta : Fin 3 → Profile 2) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict
      (restrictedPower (coupledObj K q) (liftedCoordBasis K q)
        (fun s ↦ fineWord s ∘ liftedCoordGrade q s) beta epsilon N)
      (restrictedCanonicalPower K q beta epsilon N) := by
  classical
  obtain ⟨maps, hmap, hbasis, hcoverage⟩ :=
    mme_CW_square_canonical_112_full_basis_router K q
  have hdecode : ∀ (s : Fin 3) (p : CanonicalCoord.{u} q s),
      ∃ c : DWZCanonical112Coord q s, dwzCanonical112Pair q s c = p.down.1 := by
    intro s p
    exact hcoverage s p.down.1 p.down.2
  choose decode hdecode using hdecode
  have hdata := mme_complete_split_112_coupled_basis_label_certificate K q
  apply mme_complete_split_restrictedPower_basis_router
    (canonicalObj K q) (coupledObj K q) (canonicalBasis K q) (liftedCoordBasis K q)
    maps hmap (fun s p ↦ ULift.up (decode s p)) ?_
    (canonicalLabel q) (fun s ↦ fineWord s ∘ liftedCoordGrade q s) ?_
    beta epsilon N
  · intro s p
    calc
      maps s (canonicalBasis K q s p) = maps s
          ((cwSquareCanonicalGrading K q).blockProj s (cwSquareBlockType 1 1 2 s)
            (cwSquareCanonicalBasis K q s (dwzCanonical112Pair q s (decode s p)))) := by
        rw [canonicalBasis_eq_blockProj, hdecode s p]
      _ = dwzCanonical112Vec K q s (decode s p) := hbasis s (decode s p)
      _ = liftedCoordBasis K q s (ULift.up (decode s p)) :=
        (hdata.2.2.1 s (ULift.up (decode s p))).symm
  · intro s p
    change fineWord s (coordGrade q s (decode s p)) = canonicalLabel q s p
    rw [← hdata.2.1 s (decode s p), hdecode s p]
    rfl
