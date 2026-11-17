-- Prove2me | Theorems.Thm_localGaloisToGlobal_mem_inertiaSubgroupIn
-- name    : localGaloisToGlobal_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:38.353639+00:00
-- url     : https://prove2.me/theorems/2e726b63-b9aa-48d9-869c-00bd6f114ed6
-- title:
--   Local p-adic inertia maps into global inertia at the p-adic place
-- statement:
--   Let $p$ be prime and let $τ∈\operatorname{Gal}(\overline{ℚ}_p/ℚ_p)$ lie in the inertia subgroup of the p-adic integers. Under the fixed local-to-global Galois embedding, $$\operatorname{locToGlob}_p(τ)∈I_{v_p}(\overline{ℚ}/ℚ).$$ This connects local finite-flat calculations with the global ramification conditions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_GaloisRep_CompletionBridge

set_option autoImplicit false

theorem localGaloisToGlobal_mem_inertiaSubgroupIn
    (p : ℕ) [Fact p.Prime]
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) :
    localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ := by sorry
