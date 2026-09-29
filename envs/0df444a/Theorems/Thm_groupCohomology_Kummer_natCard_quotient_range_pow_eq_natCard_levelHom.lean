-- Prove2me | Theorems.Thm_groupCohomology_Kummer_natCard_quotient_range_pow_eq_natCard_levelHom
-- name    : groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/6e71775b-3d98-54f7-a666-a6f53298cf55
-- title:
--   Kummer count: K^×/(K^×)ᵖ versus level-constant p-torsion characters
-- statement:
--   Let $k$ and $\Omega$ be fields with $\Omega$ a $k$-algebra that is Galois over $k$, let $K$ be an intermediate field of $\Omega/k$ which is finite-dimensional over $k$, and let $p$ be a natural number which is nonzero. Assume two conditions: every $\zeta \in \Omega$ with $\zeta^p = 1$ already lies in $K$, and every unit $a$ of $K$ admits a $p$-th root in $\Omega^\times$, i.e. there is $\alpha \in \Omega^\times$ with $\mathrm{algebraMap}\,K\,\Omega\,(a) = \alpha^p$. Then the cardinality of the quotient group $K^\times / \mathrm{range}(\mathrm{powMonoidHom}\,p)$, that is of $K^\times/(K^\times)^p$, equals the cardinality of the set of monoid homomorphisms $\chi$ from the fixing subgroup of $K$ in $\mathrm{Gal}(\Omega/k)$ to $\Omega^\times$ such that $\chi(\sigma)^p = 1$ for all $\sigma$, and such that there exists an intermediate field $L$ of $\Omega/k$, finite-dimensional over $k$, with $\chi(\tau) = 1$ for every $\tau$ in the fixing subgroup of $K$ whose underlying $k$-automorphism of $\Omega$ lies in the fixing subgroup of $L$. Both sides are `Nat.card`, so the assertion also covers the case in which both sets are infinite, both cardinalities then being $0$.
--
--   This is Kummer theory for $K$ containing the $p$-th roots of unity, stated as an equality of cardinalities rather than as an isomorphism: $K^\times/(K^\times)^p$ is matched with the $p$-torsion characters of $\mathrm{Gal}(\Omega/K)$ that are trivial on $\mathrm{Gal}(\Omega/L)$ for some finite $L/k$, the latter condition encoding continuity for the Krull topology. It feeds the finiteness statement [`groupCohomology.finiteDimensional_continuousH1_fixingSubgroup_of_forall_apply_eq_of_primeLocal`](thm.html#groupCohomology.finiteDimensional_continuousH1_fixingSubgroup_of_forall_apply_eq_of_primeLocal) about continuous first cohomology of the fixing subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_natCard_quotient_range_pow_eq_natCard_levelHom.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {p : ℕ} [NeZero p]
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K)
    (hroot : ∀ a : Kˣ, ∃ α : Ωˣ, algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    Nat.card (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)
      = Nat.card {χ : K.fixingSubgroup →* Ωˣ // (∀ σ, χ σ ^ p = 1) ∧
          ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
            ∀ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → χ τ = 1} := by sorry
