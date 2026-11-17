-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_of_map_injective
-- name    : groupCohomology.IsFiniteFlatCocycle.of_map_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:43.740558+00:00
-- url     : https://prove2.me/theorems/2461dec6-7434-48b7-8ba0-da7f9e047555
-- title:
--   Finite-flatness pulls back through an injective equivariant linear map
-- statement:
--   Let $p$ be prime, let $W,U$ be $ℤ/pℤ$-modules with local p-adic Galois representations $ρ,τ$, and let $c,d$ be their cocycles. Let $i:W→U$ be injective and equivariant, with $i(c(σ))=d(σ)$ for every $σ$. If $d$ is finite flat, then $$c\text{ is finite flat}.$$ This transfers finite flatness from an ambient cocycle to a submodule cocycle.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatCocycle.of_map_injective
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [Module (ZMod p) W]
    [AddCommGroup U] [Module (ZMod p) U]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (τ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U)
    (c : cocycles₁ (Rep.of ρ)) (d : cocycles₁ (Rep.of τ))
    (i : W →ₗ[ZMod p] U) (hi : Function.Injective i)
    (hiact : ∀ σ w, i (ρ σ w) = τ σ (i w))
    (hic : ∀ σ, i (c σ) = d σ)
    (hd : IsFiniteFlatCocycle p τ d) : IsFiniteFlatCocycle p ρ c := by sorry
