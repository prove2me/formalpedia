-- Prove2me | Theorems.Thm_groupCohomology_Kummer_kummerHom_surjective
-- name    : groupCohomology.Kummer.kummerHom_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/34e2ec0c-8ac2-5820-8713-b5ea4e63f5d2
-- title:
--   Surjectivity of the Kummer map for finite Galois L/K
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra that is finite-dimensional over $K$ and Galois over $K$, and let $p$ be a natural number (no primality is assumed, and no hypothesis is made on the $p$-th roots of unity in $K$). Write $G = L \simeq_{\mathrm{alg}[K]} L$ for the group of $K$-algebra automorphisms of $L$, and let `kummerRep K L p` be the $\mathbb{Z}$-linear $G$-representation obtained from the multiplicative action of $G$ on the group $\mu_p(L)$ of $p$-th roots of unity of $L$ (`rootsOfUnity p L`), written additively. Let `powerSubgroup K L p` be the subgroup of $K^\times$ consisting of those $a$ for which the image of $a$ in $L$ is a $p$-th power $\alpha^p$ of some $\alpha \in L^\times$. The monoid homomorphism `kummerHom K L p` from this subgroup to $H^1(G, \mu_p(L))$, regarded as a multiplicative group, sends $a$ to the Kummer class attached to a choice of $\alpha$ with $\mathrm{algebraMap}_{K,L}(a) = \alpha^p$, namely the class in $H^1$ of the corresponding cocycle. The theorem asserts that this homomorphism is surjective.
--
--   This is the surjectivity half of the Kummer-theoretic description of $H^1(\mathrm{Gal}(L/K), \mu_p(L))$ for a finite Galois extension $L/K$, resting on Hilbert's Theorem 90. It is used to compute the cardinality of $H^1$ as that of a quotient of $K^\times$, and in the construction of Kummer characters from continuous cohomology classes in the level-arithmetic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_kummerHom_surjective.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.kummerHom_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) :
    Function.Surjective (kummerHom K L p) := by sorry
