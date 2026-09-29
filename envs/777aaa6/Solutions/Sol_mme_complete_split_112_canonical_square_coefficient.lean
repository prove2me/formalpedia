-- Prove2me | solution 1 for mme_complete_split_112_canonical_square_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:54:01.956981+00:00
-- url     : https://prove2.me/submissions/30dae000-1e1e-4202-a44d-33958c3eb92b

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.CompleteSplit112 MME.DWZComponentRestriction Module PiTensorProduct
universe u
set_option autoImplicit false

namespace MME.CompleteSplit112

private theorem basis_eq_mpr_coe {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V] {I : Type*}
    {S T : Submodule K V} (hST : S = T)
    (h : Basis I K S = Basis I K T) (b : Basis I K T) (j : I) :
    ((Eq.mpr h b) j).val = (b j).val := by
  subst T
  rfl

private theorem canonicalBasis_coe (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p : CanonicalCoord.{u} q i) :
    (canonicalBasis K q i p).val =
      cwSquareCanonicalBasis K q i p.down.val := by
  unfold canonicalBasis
  erw [Basis.reindex_apply]
  have hs : cwBasisGrade (cwSquareCanonicalBasis K q i) (cwSquarePairGrade q)
      (cwSquareBlockType 1 1 2 i) = Submodule.span K
      (Set.range (fun a : CoarsePair q (cwSquareBlockType 1 1 2 i) ↦
        cwSquareCanonicalBasis K q i a.val)) := by
    unfold cwBasisGrade
    congr 1
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
  simp only [coarseClassBasis, id_eq]
  erw [basis_eq_mpr_coe hs]
  exact Basis.span_apply _ _

private theorem canonical_projection_coord (K : Type u) [Field K] (q : ℕ) (i : Fin 3)
    (p : CanonicalCoord.{u} q i) (x : ((CWObj K q).kron (CWObj K q)).V i) :
    (canonicalBasis K q i).repr
      ((cwSquareCanonicalGrading K q).blockProj i (cwSquareBlockType 1 1 2 i) x) p =
      (cwSquareCanonicalBasis K q i).repr x p.down.val := by
  classical
  dsimp only [canonicalObj, TensorObj.TypeGrading.blockSubtensor] at *
  let G := cwSquareCanonicalGrading K q
  let b := cwSquareCanonicalBasis K q i
  have hm : ((canonicalBasis K q i).coord p).comp
      (G.blockProj i (cwSquareBlockType 1 1 2 i)) = b.coord p.down.val := by
    apply b.ext
    intro a
    have hmem : b a ∈ G.classOf i (cwSquarePairGrade q a) :=
      Submodule.subset_span ⟨a, rfl, rfl⟩
    by_cases ha : cwSquarePairGrade q a = cwSquareBlockType 1 1 2 i
    · let pa : CanonicalCoord.{u} q i := ⟨⟨a, ha⟩⟩
      have hp : G.blockProj i (cwSquareBlockType 1 1 2 i) (b a) =
          canonicalBasis K q i pa := by
        apply Subtype.val_injective
        rw [canonicalBasis_coe]
        have h := G.blockProj_apply_mem i (cwSquareBlockType 1 1 2 i) (b a)
          (ha ▸ hmem)
        exact congrArg Subtype.val h
      change (canonicalBasis K q i).repr
        (G.blockProj i (cwSquareBlockType 1 1 2 i) (b a)) p = b.repr (b a) p.down.val
      rw [hp]
      have he : pa = p ↔ a = p.down.val := by
        constructor
        · intro h; exact congrArg (fun t : CanonicalCoord q i ↦ t.down.val) h
        · intro h; apply ULift.ext; apply Subtype.ext; exact h
      simp only [Basis.repr_self, Finsupp.single_apply, he]
    · have hz := G.blockProj_apply_mem_ne i (cwSquareBlockType 1 1 2 i)
        (cwSquarePairGrade q a) (Ne.symm ha) (b a) hmem
      have hne : a ≠ p.down.val := by
        intro h
        exact ha (h ▸ p.down.property)
      change (canonicalBasis K q i).repr
        (G.blockProj i (cwSquareBlockType 1 1 2 i) (b a)) p = b.repr (b a) p.down.val
      rw [hz]
      erw [(canonicalBasis K q i).repr.map_zero]
      simp only [Finsupp.zero_apply, Basis.repr_self,
        Finsupp.single_apply, if_neg hne]
  exact LinearMap.congr_fun hm x

/-- Canonical constituent projection preserves each coefficient in its selected coarse class. -/
theorem canonical_square_coefficient (K : Type u) [Field K] (q : ℕ)
    (p : ∀ i, CanonicalCoord.{u} q i) :
    (Basis.piTensorProduct (canonicalBasis K q)).repr (canonicalObj K q).t p =
      (Basis.piTensorProduct (cwSquareCanonicalBasis K q)).repr
        ((CWObj K q).kron (CWObj K q)).t (fun i ↦ (p i).down.val) := by
  have h (x : PiTensorProduct K ((CWObj K q).kron (CWObj K q)).V) :
      (Basis.piTensorProduct (canonicalBasis K q)).repr
        (PiTensorProduct.map (fun i ↦ (cwSquareCanonicalGrading K q).blockProj i
          (cwSquareBlockType 1 1 2 i)) x) p =
      (Basis.piTensorProduct (cwSquareCanonicalBasis K q)).repr x
        (fun i ↦ (p i).down.val) := by
    dsimp only [canonicalObj, TensorObj.TypeGrading.blockSubtensor] at *
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      rw [map_smul]
      erw [(Basis.piTensorProduct (canonicalBasis K q)).repr.map_smul]
      simp only [map_smul, map_tprod, Basis.piTensorProduct_repr_tprod_apply,
        Finsupp.smul_apply]
      apply congrArg (fun z : K ↦ a • z)
      erw [Basis.piTensorProduct_repr_tprod_apply]
      exact Finset.prod_congr rfl (fun i _ ↦ canonical_projection_coord K q i (p i) (v i))
    | add x y hx hy =>
      rw [map_add]
      erw [(Basis.piTensorProduct (canonicalBasis K q)).repr.map_add]
      simp only [map_add, Finsupp.add_apply]
      exact congrArg₂ (fun x y : K ↦ x + y) hx hy
  exact h _

end MME.CompleteSplit112

theorem solution (K : Type u) [Field K] (q : ℕ)
    (p : ∀ i, CanonicalCoord.{u} q i) :
    (Basis.piTensorProduct (canonicalBasis K q)).repr (canonicalObj K q).t p =
      (Basis.piTensorProduct (cwSquareCanonicalBasis K q)).repr
        ((CWObj K q).kron (CWObj K q)).t (fun i ↦ (p i).down.val) := by
  exact MME.CompleteSplit112.canonical_square_coefficient K q p
#print axioms solution
