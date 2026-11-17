-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_subquotient
-- name    : groupCohomology.IsFiniteFlatRepresentation.subquotient
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:57.248665+00:00
-- url     : https://prove2.me/theorems/70e225f6-c506-4428-9aaa-940b5a10ac5d
-- title:
--   Finite-flat representations are preserved by equivariant subquotients
-- statement:
--   Let $p$ be prime, let $W$ be a finite-flat local p-adic Galois representation, let $P≤W$ be a Galois-stable additive subgroup, and let $q:P→U$ be a surjective additive homomorphism satisfying $q(σw)=σq(w)$. Then $$U\text{ is a finite-flat representation}.$$ This provides the subquotient closure used for the kernel and quotient representations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatRepresentation.subquotient
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [AddCommGroup U]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U]
    (hW : IsFiniteFlatRepresentation p (fun σ (w : W) => σ • w))
    (P : AddSubgroup W)
    (hP : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W),
      w ∈ P → σ • w ∈ P)
    (q : P →+ U) (hq : Function.Surjective q)
    (hqact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : P),
      q ⟨σ • (w : W), hP σ w w.2⟩ = σ • q w) :
    IsFiniteFlatRepresentation p (fun σ (u : U) => σ • u) := by sorry
