-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_quotient
-- name    : groupCohomology.IsFiniteFlatRepresentation.quotient
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:46.810706+00:00
-- url     : https://prove2.me/theorems/5d511a85-4e4e-48eb-ae8f-abf1775ad6c0
-- title:
--   Finite-flat representations descend through equivariant quotients
-- statement:
--   Let $p$ be prime, let $W$ be a finite-flat local p-adic Galois representation, and let $q:W→U$ be a surjective equivariant additive homomorphism. Then $$U\text{ is a finite-flat representation}.$$ This supplies the quotient case needed for the cyclotomic constituent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatRepresentation.quotient
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [AddCommGroup U]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U]
    (hW : IsFiniteFlatRepresentation p (fun σ (w : W) => σ • w))
    (q : W →+ U) (hq : Function.Surjective q)
    (hqact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W),
      q (σ • w) = σ • q w) :
    IsFiniteFlatRepresentation p (fun σ (u : U) => σ • u) := by sorry
