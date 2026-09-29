-- Prove2me | Theorems.Thm_groupCohomology_natCard_torsionBy_continuousH2_units_eq_of_padic
-- name    : groupCohomology.natCard_torsionBy_continuousH2_units_eq_of_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/4d5e25e8-e35b-5738-bb43-c00352edd511
-- title:
--   The p-torsion of H²_{cts}(Gal(ℚ̄_q/K),ℚ̄_q^×) has order p
-- statement:
--   Fix a prime $q$ and an intermediate field $K$ of the extension $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ (the algebraic closure being `PadicAlgCl q`) with $K/\mathbb{Q}_q$ finite, and let $r$ be a group homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}_q/K)$, realised as the $K$-algebra automorphisms of $\overline{\mathbb{Q}}_q$, to the $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Two compatibility hypotheses are imposed on $r$: for every intermediate field $E$ of $\overline{\mathbb{Q}}_q/K$ with $E/K$ finite there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $F/\mathbb{Q}$ finite such that every $\sigma$ with $r\sigma$ in the fixing subgroup of $F$ lies in the fixing subgroup of $E$; and conversely, for every such $F$ there is such an $E$ with $\sigma$ in the fixing subgroup of $E$ implying $r\sigma$ in the fixing subgroup of $F$. Let $p$ be a further prime. Consider the group `continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))`, i.e. the quotient of the submodule `levelCocycles₂` of $2$-cocycles satisfying the level condition attached to $r$ by its intersection with the submodule `levelCoboundaries₂` of $2$-coboundaries, for the module of units of $\overline{\mathbb{Q}}_q$ with its Galois action. The assertion is that its $p$-torsion submodule, as a $\mathbb{Z}$-module, has exactly $p$ elements.
--
--   This is the statement that the $p$-torsion of the Brauer group $\mathrm{Br}(K) = H^2_{\mathrm{cts}}(\mathrm{Gal}(\overline{\mathbb{Q}}_q/K), \overline{\mathbb{Q}}_q^\times)$ of a finite extension $K$ of $\mathbb{Q}_q$ is cyclic of order $p$, for the model of the continuous $H^2$ built from cocycles satisfying a level condition transported through $r$. It feeds the computation that this $H^2$ has $\mathbb{Z}/p$-rank one and the local-global comparison of $p$-torsion classes used in the construction of the invariant map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_torsionBy_continuousH2_units_eq_of_padic.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

open groupCohomology IntermediateField

theorem groupCohomology.natCard_torsionBy_continuousH2_units_eq_of_padic
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (p : ℕ) [Fact p.Prime] :
    Nat.card (Submodule.torsionBy ℤ (continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))) (p : ℤ)) = p := by sorry
