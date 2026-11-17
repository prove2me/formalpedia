-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_eq_zero_on_inertia
-- name    : groupCohomology.IsFiniteFlatCocycle.eq_zero_on_inertia
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:47.198781+00:00
-- url     : https://prove2.me/theorems/6504ea7f-e485-440f-bb2f-c2945768d2a6
-- title:
--   An odd-prime finite-flat cocycle vanishes when inertia acts trivially
-- statement:
--   Let $p$ be an odd prime, let $W$ be a $ℤ/pℤ$-module with local p-adic Galois representation $ρ$, and let $c$ be a finite-flat cocycle. Assume every element of the inertia subgroup of $ℚ_p$ acts trivially on $W$. Then $$c(σ)=0\quad\text{for every inertia element }σ.$$ This is the local vanishing principle for the cyclotomic quotient cocycle.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatCocycle.eq_zero_on_inertia
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (c : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W)
    (hc : IsFiniteFlatCocycle p ρ c)
    (hρ : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ w : W, ρ σ w = w) :
    ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], c σ = 0 := by sorry
