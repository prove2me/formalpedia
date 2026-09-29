-- Prove2me | Theorems.Thm_groupCohomology_isLocalInv_localInv_and_bijective
-- name    : groupCohomology.isLocalInv_localInv_and_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/f67a2606-5837-5d68-b501-91f2178f0541
-- title:
--   Local invariant: normalisation and bijectivity
-- statement:
--   Fix a prime $p$ (as a `Fact`), an element $\zeta$ of $\overline{\mathbb{Q}}$ with $\zeta$ a primitive $p$-th root of unity, and a prime $q$ (again with the primality `Fact`). Write $H$ for `continuousH2` of the homomorphism `primeLocalToGlobal q`, which sends a $\mathbb{Q}_q$-automorphism of `PadicAlgCl q` to the induced automorphism of $\overline{\mathbb{Q}}$, with coefficients in the one-dimensional $\mathbb{Z}/p$-representation `ofChar` attached to the mod-$p$ cyclotomic character `cycloChar p` composed with that homomorphism; concretely $H$ is the quotient of `levelCocycles₂` by the pullback of `levelCoboundaries₂`. The assertion is twofold for the $\mathbb{Z}/p$-linear functional $H \to \mathbb{Z}/p$ defined by `localInv p ζ q` (the unique functional with the property below when such a unique one exists, and $0$ otherwise). First, `localInv p ζ q` satisfies `IsLocalInv p ζ q`: for every unit $u$ of `PadicAlgCl q` whose underlying element is the image of $\zeta$ under [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17), every finite-order $\mathbb{Q}_q$-automorphism $\varphi$ of $L = \mathbb{Q}_q(\mu_{q^p-1})$ generating the whole automorphism group (all $\sigma$ lie in `Subgroup.zpowers φ`) and acting as $x \mapsto x^q$ on the $(q^p-1)$-st roots of unity, every unit $\pi$ of $L$ with underlying element $q$, given normality of $L/\mathbb{Q}_q$, and every $2$-cocycle $z$ in `levelCocycles₂` such that the cochain $g \mapsto u^{(z\,g).\mathrm{val}}$ differs from the inflation to `PadicAlgCl q`-units of the carry cochain `carryFun φ hs hfin` applied to $\pi$ by an element of `levelCoboundaries₂`, the value of the functional on the class of $z$ is $1$. Second, `localInv p ζ q` is bijective.
--
--   This is the normalisation and isomorphism statement for the local invariant map $H^2_{\mathrm{cts}}(\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q), \mu_p) \xrightarrow{\sim} \mathbb{Z}/p$, the $p$-torsion part of the classical invariant $\mathrm{Br}(\mathbb{Q}_q) \cong \mathbb{Q}/\mathbb{Z}$ computed via the unramified cocycle built from a uniformiser and the Frobenius carry cochain. It allows the consumers of local duality — the local duality package, the restriction and theta maps on dual Selmer groups — to use this single canonical functional instead of an unspecified bijective one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isLocalInv_localInv_and_bijective.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory ExtCitation groupCohomology

theorem groupCohomology.isLocalInv_localInv_and_bijective
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime] :
    IsLocalInv p ζ q (localInv p ζ q) ∧ Function.Bijective (localInv p ζ q) := by sorry
