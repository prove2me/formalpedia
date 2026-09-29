-- Prove2me | Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn
-- name    : card_lowerRamificationGroup_zero_eq_ramificationIdxIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/57dbc8a1-52a7-50f8-a89f-bcce3d8ac191
-- title:
--   |G₀| = e for Galois Dedekind local extensions
-- statement:
--   Let $A$ be a commutative local ring which is also a Dedekind domain, and let $B$ be a commutative local ring which is a Dedekind domain, equipped with an $A$-algebra structure making $B$ a torsion-free and module-finite $A$-module. Let $G$ be a group acting on $B$ by ring automorphisms, with $G$ finite, such that `IsGaloisGroup G A B` holds, i.e. $G$ realises $B/A$ as a Galois extension in the sense of that predicate. Assume the maximal ideal of $B$ lies over the maximal ideal of $A$, and that the residue extension $(B/\mathfrak{m}_B)/(A/\mathfrak{m}_A)$ is separable. Assume finally $\mathfrak{m}_A \neq \bot$. Then the cardinality of the zeroth lower-numbering ramification group $G_0$ of $B$ relative to $G$ — which by definition is the inertia subgroup of $G$ attached to the ideal $\mathfrak{m}_B^{0+1} = \mathfrak{m}_B$, namely the subgroup of those $\sigma \in G$ with $\sigma(b) - b \in \mathfrak{m}_B$ for all $b \in B$ — equals $e$, the ramification index `ramificationIdxIn` of $\mathfrak{m}_A$ in $B$.
--
--   This is the classical identification of the order of the inertia group with the ramification index, $|G_0| = e$, in the local Galois setting with separable residue extension. It is used to convert the different-filtration formula, which is naturally expressed through $|G_0|$, into the tame statement $\mathfrak{d} = \mathfrak{m}^{e-1}$; it is cited by [`IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints`](thm.html#IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean

import Definitions.Def_DifferentFiltrationFormula
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem card_lowerRamificationGroup_zero_eq_ramificationIdxIn
    {A : Type*} [CommRing A] [IsLocalRing A]
    {B : Type*} [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    {G : Type*} [Group G] [MulSemiringAction G B]
    [IsDedekindDomain A] [Module.Finite A B] [IsGaloisGroup G A B] [Finite G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)]
    (hp : IsLocalRing.maximalIdeal A ≠ ⊥) :
    Nat.card (IsLocalRing.lowerRamificationGroup B G 0)
      = (IsLocalRing.maximalIdeal A).ramificationIdxIn B := by sorry
