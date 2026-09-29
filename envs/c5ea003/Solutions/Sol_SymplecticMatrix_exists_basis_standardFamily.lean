-- Prove2me | solution 1 for SymplecticMatrix.exists_basis_standardFamily
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T01:52:43.724094+00:00
-- url     : https://prove2.me/submissions/dd7341bd-cd52-4661-83c2-1e4fd002368a

import Definitions.Def_symplectic_block_generators
import Theorems.Thm_SymplecticMatrix_standardFamily_linearIndependent
import Theorems.Thm_SymplecticMatrix_span_standardBasisSet_eq_sp
import Theorems.Thm_SymplecticMatrix_standardGenerators_mem_sp

open SymplecticMatrix Matrix

theorem solution (l : ℕ) (R : Type*) [Field R] :
    ∃ B : Module.Basis
        ((Fin l × Fin l) ⊕
          ({p : Fin l × Fin l // p.1 ≤ p.2} ⊕ {p : Fin l × Fin l // p.1 ≤ p.2}))
        R (LieAlgebra.Symplectic.sp (Fin l) R),
      ∀ i, ((B i : LieAlgebra.Symplectic.sp (Fin l) R) :
            Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        = Sum.elim (fun p : Fin l × Fin l => elemX p.1 p.2)
            (Sum.elim (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemT p.1.1 p.1.2)
              (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemS p.1.1 p.1.2)) i := by
  classical
  -- symmetry of the symmetric block generators
  have hsymm : ∀ i j : Fin l, (symmMatrix i j : Matrix (Fin l) (Fin l) R) = symmMatrix j i := by
    intro i j
    unfold symmMatrix
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), add_comm]
  have hT : ∀ i j : Fin l,
      (elemT i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) = elemT j i := by
    intro i j; unfold elemT; rw [hsymm]
  have hS : ∀ i j : Fin l,
      (elemS i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) = elemS j i := by
    intro i j; unfold elemS; rw [hsymm]
  set mf : ((Fin l × Fin l) ⊕
      ({p : Fin l × Fin l // p.1 ≤ p.2} ⊕ {p : Fin l × Fin l // p.1 ≤ p.2}))
      → Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R :=
    Sum.elim (fun p : Fin l × Fin l => elemX p.1 p.2)
      (Sum.elim (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemT p.1.1 p.1.2)
        (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemS p.1.1 p.1.2)) with hmf
  have hmem : ∀ i, mf i ∈ LieAlgebra.Symplectic.sp (Fin l) R := by
    rintro (p | p | p)
    · exact (standardGenerators_mem_sp p.1 p.2).1
    · exact (standardGenerators_mem_sp p.1.1 p.1.2).2.1
    · exact (standardGenerators_mem_sp p.1.1 p.1.2).2.2
  set v : _ → (LieAlgebra.Symplectic.sp (Fin l) R) := fun i => ⟨mf i, hmem i⟩ with hv
  have hcomp : (fun i => ((v i : LieAlgebra.Symplectic.sp (Fin l) R) :
      Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)) = mf := rfl
  have hli : LinearIndependent R v := by
    refine LinearIndependent.of_comp
      ((LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule.subtype) ?_
    have hind := standardFamily_linearIndependent l R
    convert hind using 1
  -- the span of the family is the whole subalgebra
  have hspanset : Submodule.span R (Set.range mf)
      = (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule := by
    rw [← span_standardBasisSet_eq_sp l R]
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro x ⟨i, rfl⟩
      refine Submodule.subset_span ?_
      rcases i with p | p | p
      · exact Or.inl (Or.inl ⟨p, rfl⟩)
      · exact Or.inr ⟨(p.1.1, p.1.2), rfl⟩
      · exact Or.inl (Or.inr ⟨(p.1.1, p.1.2), rfl⟩)
    · rintro x ((⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩)
      · exact Submodule.subset_span ⟨Sum.inl p, rfl⟩
      · rcases le_total p.1 p.2 with hle | hle
        · exact Submodule.subset_span ⟨Sum.inr (Sum.inr ⟨(p.1, p.2), hle⟩), rfl⟩
        · refine Submodule.subset_span ⟨Sum.inr (Sum.inr ⟨(p.2, p.1), hle⟩), ?_⟩
          simp only [hmf, Sum.elim_inr]
          exact (hS p.1 p.2).symm
      · rcases le_total p.1 p.2 with hle | hle
        · exact Submodule.subset_span ⟨Sum.inr (Sum.inl ⟨(p.1, p.2), hle⟩), rfl⟩
        · refine Submodule.subset_span ⟨Sum.inr (Sum.inl ⟨(p.2, p.1), hle⟩), ?_⟩
          simp only [hmf, Sum.elim_inr, Sum.elim_inl]
          exact (hT p.1 p.2).symm
  have hspan : ⊤ ≤ Submodule.span R (Set.range v) := by
    intro x _
    have hmapeq : Submodule.map
        ((LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule.subtype)
        (Submodule.span R (Set.range v))
      = Submodule.span R (Set.range mf) := by
      rw [Submodule.map_span]
      congr 1
      rw [← Set.range_comp]
      rfl
    have hx : (x : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) ∈ Submodule.span R (Set.range mf) := by
      rw [hspanset]; exact x.2
    rw [← hmapeq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  exact ⟨Module.Basis.mk hli hspan, fun i => by rw [Module.Basis.mk_apply]⟩
