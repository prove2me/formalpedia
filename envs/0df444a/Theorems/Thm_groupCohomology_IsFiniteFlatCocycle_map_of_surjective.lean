-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_map_of_surjective
-- name    : groupCohomology.IsFiniteFlatCocycle.map_of_surjective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:52.445672+00:00
-- url     : https://prove2.me/theorems/f40661cf-824e-473d-9bb0-6412803eb500
-- title:
--   Finite-flat cocycles descend through surjective equivariant linear maps
-- statement:
--   Let $p$ be prime, let $W,U$ be $ℤ/pℤ$-modules with local p-adic Galois representations $ρ,τ$, and let $c,d$ be their cocycles. Let $q:W→U$ be a surjective linear map satisfying $q(ρ(σ)w)=τ(σ)q(w)$ and $q(c(σ))=d(σ)$ for every $σ,w$. If $c$ is finite flat, then $$d\text{ is finite flat}.$$ This transports finite flatness to quotient cocycles.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatCocycle.map_of_surjective
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [Module (ZMod p) W]
    [AddCommGroup U] [Module (ZMod p) U]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (τ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U)
    (c : cocycles₁ (Rep.of ρ)) (d : cocycles₁ (Rep.of τ))
    (q : W →ₗ[ZMod p] U) (hq : Function.Surjective q)
    (hqact : ∀ σ w, q (ρ σ w) = τ σ (q w))
    (hqc : ∀ σ, q (c σ) = d σ)
    (hc : IsFiniteFlatCocycle p ρ c) : IsFiniteFlatCocycle p τ d := by sorry
