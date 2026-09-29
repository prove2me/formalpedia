-- Prove2me | Theorems.Thm_groupCohomology_Kummer_ker_kummerHom
-- name    : groupCohomology.Kummer.ker_kummerHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/598d6dbf-44e7-5d3a-b2d2-4106ab89ea27
-- title:
--   Kernel of the Kummer map is the group of p-th powers
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra such that $L/K$ is Galois (in the `IsGalois` sense, so possibly infinite), and let $p$ be a natural number. Write $G = L \simeq_{\mathrm{alg}[K]} L$ for the Galois group and let `kummerRep K L p` be the $\mathbb{Z}$-linear representation of $G$ obtained from its multiplicative–distributive action on the group $\mu_p(L)$ of $p$-th roots of unity in $L$. Let `powerSubgroup K L p` be the subgroup of $K^\times$ consisting of those units $a$ whose image $\mathrm{algebraMap}\,K\,L\,(a)$ in $L$ is of the form $\alpha^p$ for some $\alpha \in L^\times$, and let `kummerHom K L p` be the homomorphism from this subgroup to $H^1(G, \mu_p(L))$ (written multiplicatively via `Multiplicative`) sending $a$ to the Kummer class attached to a chosen $p$-th root $\alpha$ of the image of $a$. The theorem asserts that the kernel of `kummerHom K L p` is exactly the subgroup of `powerSubgroup K L p` cut out by the range of the $p$-th power map $K^\times \to K^\times$: that is, an element $a$ of `powerSubgroup K L p` has trivial Kummer class if and only if $a = b^p$ for some $b \in K^\times$.
--
--   This is the injectivity half of Kummer theory in cohomological form: the Kummer map induces an injection of $\bigl(K^\times \cap (L^\times)^p\bigr)/(K^\times)^p$ into $H^1(\mathrm{Gal}(L/K), \mu_p(L))$. It is used to compute the cardinality of that $H^1$ as the cardinality of the corresponding quotient group, in [`groupCohomology.Kummer.natCard_H1_eq_natCard_quotient`](thm.html#groupCohomology.Kummer.natCard_H1_eq_natCard_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_ker_kummerHom.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.ker_kummerHom
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] (p : ℕ) :
    (kummerHom K L p).ker
      = ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p) := by sorry
