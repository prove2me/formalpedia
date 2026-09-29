-- Prove2me | Theorems.Thm_groupCohomology_existsUnique_isLocalInv
-- name    : groupCohomology.existsUnique_isLocalInv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/bfd6c0e9-08b5-5d70-9387-881aa2dfafb8
-- title:
--   Unique local invariant functional on continuous H² at q
-- statement:
--   Let $p$ be a prime, let $\zeta$ be an element of $\overline{\mathbb{Q}}$ that is a primitive $p$-th root of unity, and let $q$ be a prime. Write $G_q = \mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ for `primeLocalGaloisGroup q` and $r_q =$ `primeLocalToGlobal q` for the homomorphism $G_q \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to the algebraic closure of $\mathbb{Q}$, and let $M$ be the one-dimensional representation `ofChar` of $G_q$ over $\mathbb{Z}/p$ given by the trivial representation twisted by the character $(\mathrm{cycloChar}\,p)\circ r_q$, i.e. by the mod $p$ cyclotomic character of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ pulled back along $r_q$. The assertion is that there is exactly one $\mathbb{Z}/p$-linear map $f$ from `continuousH2 r_q M` — the quotient of the level-$r_q$ $2$-cocycles `levelCocycles₂` by those that are level $2$-coboundaries — to $\mathbb{Z}/p$ satisfying the predicate `IsLocalInv p ζ q f`: for every unit $u$ of $\overline{\mathbb{Q}}_q$ whose underlying element is the image $\iota_q(\zeta)$ of $\zeta$ under [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17), every $\mathbb{Q}_q$-automorphism $\varphi$ of $E = \mathbb{Q}_q\big(\{x : x^{q^p-1}=1\}\big)$ that generates the full automorphism group of $E$, has finite order and acts as $x \mapsto x^{q}$ on the $(q^p-1)$-st roots of unity, every unit $\pi$ of $E$ whose image in $\overline{\mathbb{Q}}_q$ is $q$, and granted that $E/\mathbb{Q}_q$ is normal, every level $2$-cocycle $z : G_q \times G_q \to \mathbb{Z}/p$ for $M$ such that the difference of $(g_1,g_2) \mapsto u^{z(g_1,g_2)}$ (written additively) and the inflation to $G_q$ of the cyclic carry cochain `carryFun` of $\varphi$ with value $\pi$ — which is $\pi$ when the sum of the cyclic logarithms of the two arguments is at least the order of $\varphi$, and $1$ otherwise — is a level $2$-coboundary for the $G_q$-module $\overline{\mathbb{Q}}_q^{\times}$, the value of $f$ on the class of $z$ is $1$.
--
--   This is the local invariant map of local class field theory, restricted to the $p$-torsion of the Brauer group of $\mathbb{Q}_q$ in $\mathbb{Z}/p(\chi_p)$-coefficients and normalised so that the class built from the arithmetic Frobenius of the unramified degree-$p$ extension $\mathbb{Q}_q(\mu_{q^p-1})$, the uniformiser $q$ and the $p$-th root of unity $\iota_q(\zeta)$ has invariant $1$. It is used by [`groupCohomology.isLocalInv_localInv_and_bijective`](thm.html#groupCohomology.isLocalInv_localInv_and_bijective), which identifies the resulting functional as an isomorphism and thereby supplies the local pairing at $q$ for the dual Selmer group computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_existsUnique_isLocalInv.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory ExtCitation groupCohomology

theorem groupCohomology.existsUnique_isLocalInv
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime] :
    ∃! f : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p, IsLocalInv p ζ q f := by sorry
