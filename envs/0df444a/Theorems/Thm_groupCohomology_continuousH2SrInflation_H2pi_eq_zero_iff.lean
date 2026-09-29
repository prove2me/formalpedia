-- Prove2me | Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff
-- name    : groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/5fd7e26f-a626-5f42-b187-7ca2d85c9aa2
-- title:
--   Inflated H²_S class vanishes iff cocycle bounds deeper
-- statement:
--   Fix a commutative ring $k$, a group $G$, a homomorphism $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the absolute Galois group realised as $\overline{\mathbb{Q}}$-automorphisms over $\mathbb{Q}$), a finite set $S$ of rational primes, and a $k$-linear representation $M$ of $G$. For an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, write $U_F = r^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F))$ for the comap along $r$ of the fixing subgroup of $F$, and call $F$ unramified outside $S$ when $F/\mathbb{Q}$ is finite and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ lies in $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$. Assume $M$ is smooth for these levels: every $m \in M$ is fixed by $U_{F_0}$ for some $F_0$ unramified outside $S$. Let $F$ be unramified outside $S$ and normal over $\mathbb{Q}$, and let $f$ be a $2$-cocycle of the quotient representation of $G/U_F$ on the $U_F$-invariants $M^{U_F}$. Then the inflation of the class $[f]$ into the $S$-ramified continuous $H^2$ of $r$ on $M$ (the quotient of $S$-level $2$-cocycles by those $S$-level $2$-coboundaries) vanishes if and only if there are an intermediate field $F' \supseteq F$ unramified outside $S$ with $F'/\mathbb{Q}$ Galois and a function $y \colon G/U_{F'} \to M^{U_{F'}}$, subject to no further condition, with $f(\bar g, \bar h) = \rho(g)\,y(\bar h) - y(\overline{gh}) + y(\bar g)$ in $M$ for all $g, h \in G$, the classes being taken modulo $U_F$ on the left and modulo $U_{F'}$ on the right.
--
--   This is the kernel half of the identification of the $S$-ramified continuous $H^2$ attached to $r$ and $M$ with the direct limit of the finite-level groups $H^2(G/U_F, M^{U_F})$ over fields $F$ unramified outside $S$: an inflated class dies exactly when its cocycle becomes a coboundary after passing to a deeper Galois level, the bounding $1$-cochain being written explicitly. It is used in the level-arithmetic results on restricting coboundaries and comparing inflations, and in the companion surjectivity statement for inflation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) [Normal ℚ F]
    (f : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2SrInflation r S M F hF (H2π _ f) = 0 ↔
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (G ⧸ F'.fixingSubgroup.comap r) → M.quotientToInvariants (F'.fixingSubgroup.comap r)),
      ∀ g h : G, ((f ((g : G ⧸ F.fixingSubgroup.comap r), (h : G ⧸ F.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
        = M.ρ g (y (h : G ⧸ F'.fixingSubgroup.comap r)) - (y ((g * h : G) : G ⧸ F'.fixingSubgroup.comap r) : M) + y (g : G ⧸ F'.fixingSubgroup.comap r) := by sorry
