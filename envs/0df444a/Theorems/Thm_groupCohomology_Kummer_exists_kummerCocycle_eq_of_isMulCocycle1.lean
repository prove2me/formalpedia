-- Prove2me | Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1
-- name    : groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/db2b8f60-d9c7-5a18-aef8-fa0ac91867a1
-- title:
--   Surjectivity of the Kummer map via Hilbert 90
-- statement:
--   Let $K$ be a field and $L$ a finite-dimensional Galois extension of $K$, let $p$ be a natural number, and let $f \colon \mathrm{Gal}(L/K) \to L^{\times}$, written on the automorphism group $L \simeq_{\mathrm{alg}[K]} L$, be a multiplicative $1$-cocycle for the natural action of the Galois group on $L^{\times}$ (the predicate `IsMulCocycle₁`, i.e. $f(\sigma\tau) = \sigma(f(\tau)) \cdot f(\sigma)$ in Mathlib's convention). Assume in addition that $f(\sigma)^{p} = 1$ for every $\sigma \in \mathrm{Gal}(L/K)$. The conclusion asserts the existence of a unit $a \in K^{\times}$ and a unit $\alpha \in L^{\times}$ such that the image of $a$ under the structure map $K \to L$ equals $\alpha^{p}$ in $L$, and such that for every $\sigma$ one has $f(\sigma) = \sigma \cdot \alpha / \alpha$, the value at $\sigma$ of `kummerCocycle α`, which is defined to be exactly the quotient $(\sigma \bullet \alpha)/\alpha$ in $L^{\times}$. No primality is assumed of $p$; for $p = 0$ the hypothesis on $f$ is vacuous and the conclusion reduces to Hilbert's Theorem 90 with $a = 1$.
--
--   This is the surjectivity half of the Kummer description of $p$-torsion cocycles: a $1$-cocycle of a finite Galois group valued in $L^{\times}$ and killed by $p$ arises from a $p$-th root $\alpha$ of an element of $K^{\times}$. It is used to produce Kummer classes, via [`groupCohomology.Kummer.exists_kummerClass_eq`](thm.html#groupCohomology.Kummer.exists_kummerClass_eq) and the level-refined variant [`groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_of_level`](thm.html#groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_of_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f) (hfp : ∀ σ : L ≃ₐ[K] L, f σ ^ p = 1) :
    ∃ (a : Kˣ) (α : Lˣ),
      algebraMap K L (a : K) = (α : L) ^ p ∧ ∀ σ : L ≃ₐ[K] L, f σ = kummerCocycle α σ := by sorry
