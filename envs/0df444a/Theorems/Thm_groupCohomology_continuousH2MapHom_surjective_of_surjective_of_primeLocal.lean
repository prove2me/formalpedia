-- Prove2me | Theorems.Thm_groupCohomology_continuousH2MapHom_surjective_of_surjective_of_primeLocal
-- name    : groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/d8e3aa02-545d-525d-911f-ecb84a0d7c76
-- title:
--   Surjectivity of continuous H² for local Galois subgroups
-- statement:
--   Fix a prime $p$ and a prime $q$, and let $G_q$ denote `primeLocalGaloisGroup q`, the group of $\mathbb{Q}_q$-algebra automorphisms of a fixed algebraic closure `PadicAlgCl` $q$ of $\mathbb{Q}_q$. Let $S \le G_q$ be a subgroup, and write $r$ for the homomorphism $S \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by composing the inclusion of $S$ with `primeLocalToGlobal q`, the map sending an automorphism to its restriction of scalars to $\mathbb{Q}$ followed by `AlgEquiv.restrictNormalHom` to `AlgebraicClosure ℚ`. Assume (hypothesis `hS`) that there is an intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose fixing subgroup has preimage under `primeLocalToGlobal q` contained in $S$. Let $\psi : B \to C$ be a morphism of $\mathbb{Z}/p$-linear representations of $S$, with $B$ finite-dimensional over $\mathbb{Z}/p$ (no finiteness is assumed of $C$), such that: every $b \in B$ admits an intermediate field $F$, finite-dimensional over $\mathbb{Q}$, with $B.\rho(s)\,b = b$ for all $s \in S$ whose image $r(s)$ fixes $F$ pointwise; and the underlying map $\psi$ of modules is surjective. The conclusion is that the induced $\mathbb{Z}/p$-linear map `continuousH2MapHom` on continuous second cohomology — the quotient of the level cocycles `levelCocycles₂` $r\,(-)$ by the level coboundaries, functorially in the representation — is surjective from that of $B$ onto that of $C$.
--
--   This is the right-exactness of continuous $H^2(S,-)$ on smooth finite $p$-torsion coefficient modules for open subgroups $S$ of a local Galois group, the degree-$\le 2$ shadow of $\operatorname{cd}_p$ of a $p$-adic local field being $2$. It is stated for arbitrary such $S$ so as to apply at every level, and feeds the local Euler-characteristic and duality computations used in the deformation-theoretic bookkeeping, being cited by the statements on $\theta$ for the dual twist at a Sylow level, on the local restriction maps spanning continuous $H^2$, and on the rank formula for continuous classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_continuousH2MapHom_surjective_of_surjective_of_primeLocal.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.continuousH2MapHom_surjective_of_surjective_of_primeLocal
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    {B C : Rep (ZMod p) S} (ψ : B ⟶ C) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hψ : Function.Surjective ψ.hom) :
    Function.Surjective (continuousH2MapHom ((primeLocalToGlobal q).comp S.subtype) ψ) := by sorry
