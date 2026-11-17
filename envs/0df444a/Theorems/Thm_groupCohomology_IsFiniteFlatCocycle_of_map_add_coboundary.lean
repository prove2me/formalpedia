-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_of_map_add_coboundary
-- name    : groupCohomology.IsFiniteFlatCocycle.of_map_add_coboundary
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:51.001073+00:00
-- url     : https://prove2.me/theorems/542e9085-079d-4977-a09d-5a7e35d985d1
-- title:
--   Finite-flatness pulls back when the mapped cocycle differs by a coboundary
-- statement:
--   Let $p$ be prime, let $W,U$ be $ℤ/pℤ$-modules with local p-adic Galois representations $ρ,τ$, let $i:W→U$ be injective and equivariant, and let $c,d$ be cocycles. Suppose there is $b∈U$ such that $d(σ)=i(c(σ))+τ(σ)b-b$ for every $σ$. If $d$ is finite flat, then $$c\text{ is finite flat}.$$ This makes finite flatness invariant under the mapped cohomology-class relation used in the Kummer argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatCocycle.of_map_add_coboundary
    (p : ℕ) [Fact p.Prime]
    {W U : Type} [AddCommGroup W] [Module (ZMod p) W]
    [AddCommGroup U] [Module (ZMod p) U]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (τ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) U)
    (c : cocycles₁ (Rep.of ρ)) (d : cocycles₁ (Rep.of τ))
    (i : W →ₗ[ZMod p] U) (hi : Function.Injective i)
    (hiact : ∀ σ w, i (ρ σ w) = τ σ (i w))
    (b : U) (hic : ∀ σ, d σ = i (c σ) + (τ σ b - b))
    (hd : IsFiniteFlatCocycle p τ d) : IsFiniteFlatCocycle p ρ c := by sorry
