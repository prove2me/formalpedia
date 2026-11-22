-- Prove2me | Definitions.Def_BruhatTits_Lattice_Quotient
-- name    : BruhatTits_Lattice_Quotient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T10:56:37.271508+00:00
-- url     : https://prove2.me/theorems/5fa7f3b0-80b9-47a5-91e4-c3f9cdcde76e
-- title:
--   Quotient
-- statement:
--   Definitions and structural lemmas for Quotient, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Theorems.Thm_Basis_transvectEquiv_mem_of_mem
import Theorems.Thm_quotient_finrank_eq

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]
namespace BruhatTits
set_option synthInstance.maxHeartbeats 30000
def Lattice.quotient (L : BruhatTits.Lattice R) : Type _ :=
  L.M ⧸ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M)
instance (L : BruhatTits.Lattice R) : AddCommGroup L.quotient :=
  inferInstanceAs <| AddCommGroup (L.M ⧸ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M))
instance Lattice.quotientModule (L : BruhatTits.Lattice R) : Module R L.quotient :=
  inferInstanceAs <| Module R (L.M ⧸ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M))
def Lattice.toQuotient (L : BruhatTits.Lattice R) : L.M →ₗ[R] L.quotient :=
  (IsLocalRing.maximalIdeal R • ⊤ : Submodule R L.M).mkQ
open IsLocalRing
instance (L : BruhatTits.Lattice R) : Module (ResidueField R) L.quotient :=
  inferInstanceAs <|
    Module (R ⧸ maximalIdeal R) (L.M ⧸ (maximalIdeal R • ⊤ : Submodule R L.M))
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000
instance (priority := 9999999) : SMul (↥R) (↥R ⧸ maximalIdeal ↥R) :=
  Submodule.Quotient.instSMul (maximalIdeal ↥R)
instance (priority := 9999999) (L : BruhatTits.Lattice R) :
    SMul (↥R ⧸ maximalIdeal ↥R) (↥L.M ⧸ (maximalIdeal ↥R • ⊤ : Submodule R L.M)) :=
  (Module.instQuotientIdealSubmoduleHSMulTop (↥L.M) (maximalIdeal ↥R)).toSMul
set_option synthInstance.maxHeartbeats 100000 in
instance (L : BruhatTits.Lattice R) : IsScalarTower R (ResidueField R) L.quotient :=
  inferInstanceAs <|
    IsScalarTower R (R ⧸ maximalIdeal R) (L.M ⧸ (maximalIdeal R • ⊤ : Submodule R L.M))
lemma Lattice.quotient_finrank [IsFractionRing R K] (L : BruhatTits.Lattice R) :
    Module.finrank (ResidueField R) L.quotient = 2 := by
  show Module.finrank (R ⧸ maximalIdeal R) (L.M ⧸ (maximalIdeal R • ⊤ : Submodule R L.M)) =
    Fintype.card (Fin 2)
  apply quotient_finrank_eq
  exact L.basis
def _root_.Basis.toQuotient [IsFractionRing R K] {L : BruhatTits.Lattice R} (b : Basis (Fin 2) R L.M) :
    Basis (Fin 2) (ResidueField R) L.quotient :=
  let v (i : Fin 2) : L.quotient := L.toQuotient (b i)
  have hsp : ⊤ ≤ Submodule.span (ResidueField R) (Set.range v) := by
    rintro x -
    refine Quotient.inductionOn' x (fun x ↦ ?_)
    have hx : x ∈ Submodule.span R (Set.range b) := by
      rw [b.span_eq]
      trivial
    induction' hx using Submodule.span_induction with x hx x y _ _ hx hy a x _ hx
    · obtain ⟨i, rfl⟩ := hx
      apply Submodule.subset_span
      use i
      rfl
    · exact Submodule.zero_mem _
    · exact Submodule.add_mem _ hx hy
    · exact Submodule.smul_mem _ (Ideal.Quotient.mk _ a) hx
  have hli : LinearIndependent (ResidueField R) v := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hsp
    exact L.quotient_finrank.symm
  Basis.mk hli hsp
instance [IsFractionRing R K] (L : BruhatTits.Lattice R) : Module.Free (ResidueField R) L.quotient :=
  Module.Free.of_basis L.basis.toQuotient
instance [IsFractionRing R K] (L : BruhatTits.Lattice R) : Module.Finite (ResidueField R) L.quotient := by
  apply Module.finite_of_finrank_eq_succ
  rw [L.quotient_finrank]
def _root_.Basis.toQuotient' [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K)) :
    Basis (Fin 2) (ResidueField R) (b.toLattice (R := R)).quotient :=
  (b.restrictToLattice (R := R)).toQuotient
def _root_.Basis.transvectResidue [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    Basis (Fin 2) (ResidueField R) (b.toLattice (R := R)).quotient :=
  let bQ := b.toQuotient' (R := R)
  bQ.transvect (Ideal.Quotient.mk _ x)
def _root_.Basis.unipotentResidue [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (b.toLattice (R := R)).quotient ≃ₗ[ResidueField R] (b.toLattice (R := R)).quotient :=
  let bQ := b.toQuotient' (R := R)
  Module.Basis.equiv bQ (b.transvectResidue x) (Equiv.refl _)
lemma _root_.Basis.transvectEquiv_apply_mem (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (y : b.toSubmodule (R := R)) :
    b.transvectEquiv x y ∈ b.toSubmodule (R := R) := by
  apply b.transvectEquiv_mem_of_mem
  exact y.property
def Lattice.mapIntermediateSubmodule (L : BruhatTits.Lattice R) (M : Submodule R (Fin 2 → K)) :
    Submodule (ResidueField R) L.quotient :=
  let M' : Submodule R (L.M ⧸ (maximalIdeal R • ⊤ : Submodule R L.M)) :=
    (M.comap L.M.subtype).map L.toQuotient
  {
    toAddSubmonoid := M'.toAddSubmonoid
    smul_mem' := by
      intro c x hx
      refine Quotient.inductionOn' c (fun c ↦ ?_)
      show c • x ∈ M'
      exact M'.smul_mem c hx
  }
def Lattice.mapIntermediate (L M : BruhatTits.Lattice R) :
    Submodule (ResidueField R) L.quotient :=
  L.mapIntermediateSubmodule M.M
def _root_.Basis.quotientStdLine₀ (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    Submodule (ResidueField R) (b.toLattice (R := R)).quotient :=
  (b.toLattice (R := R)).mapIntermediate (b.ntwist₂ hϖ 1 0).toLattice
def _root_.Basis.quotientStdLine₁ (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    Submodule (ResidueField R) (b.toLattice (R := R)).quotient :=
  (b.toLattice (R := R)).mapIntermediate (b.ntwist₂ hϖ 0 1).toLattice
open Pointwise
variable [IsFractionRing R K]
end BruhatTits


