-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatRepresentation_subobject
-- name    : groupCohomology.IsFiniteFlatRepresentation.subobject
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:42.737251+00:00
-- url     : https://prove2.me/theorems/6f3fa56a-45f4-49e7-91ce-6fda6da1dff5
-- title:
--   Equivariant subrepresentations of finite-flat representations are finite flat
-- statement:
--   Let $p$ be prime, let $U$ be a finite-flat local p-adic Galois representation, and let $i:W→U$ be an injective equivariant additive homomorphism. Then $$W\text{ is a finite-flat representation}.$$ This supplies the subobject closure needed for the kernel constituent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatRepresentation.subobject
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [AddCommGroup U]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U]
    (hU : IsFiniteFlatRepresentation p (fun σ (u : U) => σ • u))
    (i : W →+ U) (hi : Function.Injective i)
    (hiact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W),
      i (σ • w) = σ • i w) :
    IsFiniteFlatRepresentation p (fun σ (w : W) => σ • w) := by sorry
