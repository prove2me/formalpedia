-- Prove2me | Theorems.Thm_groupCohomology_isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar
-- name    : groupCohomology.isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/559778a5-c1b2-5b28-9351-df8fd1f671da
-- title:
--   Multiplicative μₚ-cocycles versus additive cocycles of 𝔽ₚ(χ)
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $p$ be a prime, and let $\chi\colon (L\simeq_{\mathrm{alg}[K]}L)\to(\mathbb{Z}/p)^{\times}$ be a group homomorphism from the group of $K$-algebra automorphisms of $L$ to the units of $\mathbb{Z}/p$. Let $\zeta\in L^{\times}$ be a primitive $p$-th root of unity, and assume that every $g$ in that automorphism group acts on $\zeta$ by $g\cdot\zeta=\zeta^{(\chi(g))\,\mathrm{val}}$, where for $a\in\mathbb{Z}/p$ the natural number $a.\mathrm{val}$ is the representative in $\{0,\dots,p-1\}$. Let $c\colon (L\simeq_{\mathrm{alg}[K]}L)\to\mathbb{Z}/p$ be any function. The assertion is that the $L^{\times}$-valued function $g\mapsto\zeta^{(c(g)).\mathrm{val}}$ satisfies the multiplicative $1$-cocycle condition $f(gh)=\bigl(g\cdot f(h)\bigr)\,f(g)$ for all $g,h$ if and only if $c$ lies in the group of additive $1$-cocycles of the representation `ofChar` $\chi$, namely the trivial one-dimensional representation of the automorphism group over $\mathbb{Z}/p$ twisted by $\chi$, in which $g$ acts on $x\in\mathbb{Z}/p$ by $x\mapsto \chi(g)\,x$; explicitly, $c(gh)=\chi(g)\,c(h)+c(g)$ for all $g,h$.
--
--   This is the additive–multiplicative dictionary identifying $Z^{1}(G,\mu_p)$ with $Z^{1}(G,\mathbb{F}_p(\chi))$ after a choice of primitive $p$-th root of unity, with $G$ the group of $K$-automorphisms of $L$. It is used in the computation of Selmer-type local conditions, feeding [`groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two`](thm.html#groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two) and [`groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot`](thm.html#groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar.lean

import Mathlib
import Definitions.Def_DualSelmer_ExtConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology

theorem groupCohomology.isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar
    {K L : Type} [Field K] [Field L] [Algebra K L] {p : ℕ} [Fact p.Prime]
    (χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ) {ζ : Lˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val) (c : (L ≃ₐ[K] L) → ZMod p) :
    IsMulCocycle₁ (fun g => ζ ^ (c g).val) ↔ c ∈ cocycles₁ (ofChar χ) := by sorry
