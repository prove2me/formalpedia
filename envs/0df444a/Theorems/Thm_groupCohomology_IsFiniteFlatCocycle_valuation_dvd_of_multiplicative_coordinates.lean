-- Prove2me | Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_valuation_dvd_of_multiplicative_coordinates
-- name    : groupCohomology.IsFiniteFlatCocycle.valuation_dvd_of_multiplicative_coordinates
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:44.261205+00:00
-- url     : https://prove2.me/theorems/257491d4-fb5d-4dff-84fc-8299a6faa43e
-- title:
--   Finite-flat Kummer coordinates force p-divisibility of the p-adic valuation
-- statement:
--   Let $p$ be an odd prime, let $W$ be a $ℤ/pℤ$-module with local Galois representation $ρ$, and let $c$ be a finite-flat cocycle. Assume an injective map $μ:W→\overline{ℚ}_p$ satisfies $μ(0)=1$, $μ(v+w)=μ(v)μ(w)$, $μ(w)^p=1$, and $μ(ρ(σ)w)=σμ(w)$. Let $x∈ℚ_p$ and $γ∈\overline{ℚ}_p$ satisfy $γ^p=x$ and $μ(c(σ))γ=σγ$ for every $σ$. Then $$p\mid v_p(x).$$ This is the finite-flat local Kummer criterion used to prove global $71$st-power divisibility.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
import Theorems.Thm_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.IsFiniteFlatCocycle.valuation_dvd_of_multiplicative_coordinates
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Representation (ZMod p) (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) W)
    (c : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W)
    (hc : IsFiniteFlatCocycle p ρ c)
    (μ : W → PadicAlgCl p) (hμinj : Function.Injective μ)
    (hμzero : μ 0 = 1) (hμadd : ∀ v w, μ (v + w) = μ v * μ w)
    (hμroot : ∀ w, μ w ^ p = 1)
    (hμact : ∀ σ w, μ (ρ σ w) = σ (μ w))
    (x : ℚ_[p]) (γ : PadicAlgCl p)
    (hγ : γ ^ p = algebraMap ℚ_[p] (PadicAlgCl p) x)
    (hKummer : ∀ σ, μ (c σ) * γ = σ γ) :
    (p : ℤ) ∣ Padic.valuation x := by sorry
