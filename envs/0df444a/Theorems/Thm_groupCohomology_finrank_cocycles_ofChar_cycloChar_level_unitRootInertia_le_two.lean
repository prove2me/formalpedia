-- Prove2me | Theorems.Thm_groupCohomology_finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
-- name    : groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/b0170c1f-a233-5fdb-b2ac-f456c6236b13
-- title:
--   Unit-inertia finite-level cocycles in 𝔽ₚ(ω) span at most a plane
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $G_p$ denote the group of $\mathbb{Q}_p$-algebra automorphisms of the algebraic closure `PadicAlgCl p`, mapped to the absolute Galois group of $\mathbb{Q}$ by `primeLocalToGlobal (pPrime p)` (restriction of scalars followed by restriction to the algebraic closure of $\mathbb{Q}$). Write $\omega$ for the composite of that map with the mod $p$ cyclotomic character `cycloChar p`, and let `ofChar` of $\omega$ be the one-dimensional $\mathbb{Z}/p$-representation of $G_p$ given by the trivial representation on $\mathbb{Z}/p$ twisted by $\omega$, i.e. $g$ acting as multiplication by $\omega(g)$. Let $Z$ be a $\mathbb{Z}/p$-submodule of the module of $1$-cocycles of this representation, and assume $Z$ consists exactly of those cocycles $c$ such that (i) $c$ has finite level: there is an intermediate field $F$ of the algebraic closure of $\mathbb{Q}$, finite over $\mathbb{Q}$, with $c(gs) = c(g)$ for all $g, s \in G_p$ whose image of $s$ lies in the fixing subgroup of $F$; and (ii) $c$ vanishes on [`ResidualGaloisRep.unitRootInertia p`](def/GaloisRep_OrdinaryUnitClasses.html#L17), the set of $\sigma \in G_p$ lying in the inertia subgroup of the valuation subring of `PadicAlgCl p` over $\mathbb{Q}_p$, fixing every $p$-th root of unity, and fixing every element $\beta$ of norm $1$ whose $p$-th power is fixed by the whole inertia subgroup. Then $Z$ is finite-dimensional over $\mathbb{Z}/p$ and $\operatorname{finrank}_{\mathbb{Z}/p} Z \leq 2$.
--
--   This is the dimension bound for the space of finite-level, "peu ramifié" (unit-root inertia trivial) $1$-cocycles of the local Galois group at $p$ with values in $\mathbb{F}_p(\omega)$, the Kummer-theoretic incarnation of $\mathbb{Q}_p^\times/(\mathbb{Q}_p^\times)^p$ being two-dimensional for odd $p$. It is used to derive [`groupCohomology.finrank_span_H1_unitRootInertia_le_one`](thm.html#groupCohomology.finrank_span_H1_unitRootInertia_le_one), the corresponding bound of $1$ on the relevant subspace of $H^1$ after quotienting by coboundaries.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory TrivSqZeroExt ExtCitation
open groupCohomology

theorem groupCohomology.finrank_cocycles_ofChar_cycloChar_level_unitRootInertia_le_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Z : Submodule (ZMod p)
      (cocycles₁ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal (pPrime p))))))
    (hZ : ∀ c, c ∈ Z ↔
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup (pPrime p)),
          primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
      ∀ σ ∈ ResidualGaloisRep.unitRootInertia p, c.val σ = 0) :
    FiniteDimensional (ZMod p) Z ∧ Module.finrank (ZMod p) Z ≤ 2 := by sorry
