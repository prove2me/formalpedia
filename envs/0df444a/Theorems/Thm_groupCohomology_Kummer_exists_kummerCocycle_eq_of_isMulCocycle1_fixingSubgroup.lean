-- Prove2me | Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup
-- name    : groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/d4b5bcfa-10cd-5700-a453-4aefaa758d1b
-- title:
--   Kummer description of p-torsion cocycles on a fixing subgroup
-- statement:
--   Let $\Omega/k$ be a Galois extension of fields, let $K$ be an intermediate field of $\Omega/k$ that is finite-dimensional over $k$, and let $p$ be a nonzero natural number. Write $U =$ `K.fixingSubgroup` for the subgroup of $\Omega \simeq_{\text{alg}[k]} \Omega$ fixing $K$ pointwise, acting on $\Omega^{\times}$ in the evident way. Let $f : U \to \Omega^{\times}$ be a function which is a multiplicative $1$-cocycle, i.e. $f(\sigma\tau) = (\sigma \cdot f(\tau)) \, f(\sigma)$ for all $\sigma, \tau \in U$, whose values are $p$-torsion, $f(\sigma)^p = 1$ for every $\sigma$, and which is assumed locally constant in the following sense: there exists an intermediate field $L$ of $\Omega/k$, finite-dimensional over $k$, such that $f(\sigma\tau) = f(\sigma)$ for all $\sigma, \tau \in U$ whose second member, viewed as an element of $\Omega \simeq_{\text{alg}[k]} \Omega$, lies in `L.fixingSubgroup`. The conclusion is that there exist a unit $a \in K^{\times}$ and a unit $\alpha \in \Omega^{\times}$ with $\operatorname{algebraMap}_{K,\Omega}(a) = \alpha^{p}$ in $\Omega$ and with $f(\sigma) = (\sigma \cdot \alpha)/\alpha$, the value of `kummerCocycle α` at the underlying $k$-automorphism of $\sigma$, for every $\sigma \in U$.
--
--   This is the surjectivity half of Kummer theory for $H^1(\mathrm{Gal}(\Omega/K), \mu_p)$, stated for the fixing subgroup $U \le \mathrm{Gal}(\Omega/k)$ rather than for $\mathrm{Gal}(\Omega/K)$ itself, with continuity of the cocycle encoded by invariance under the fixing subgroup of one finite subextension $L/k$. It feeds the corresponding statement for homomorphisms, [`groupCohomology.Kummer.exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup`](thm.html#groupCohomology.Kummer.exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {p : ℕ} [NeZero p]
    {f : K.fixingSubgroup → Ωˣ} (hf : IsMulCocycle₁ f) (hfp : ∀ σ, f σ ^ p = 1)
    (hlc : ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
      ∀ σ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → f (σ * τ) = f σ) :
    ∃ (a : Kˣ) (α : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p ∧
      ∀ σ : K.fixingSubgroup, f σ = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by sorry
