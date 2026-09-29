-- Prove2me | Theorems.Thm_groupCohomology_unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd
-- name    : groupCohomology.unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/48abbe9f-485d-56d6-9a6b-2fe05e18b967
-- title:
--   Inflated carry cochain restricts to a level coboundary over E
-- statement:
--   Fix a prime $q$ and a finite extension $K$ of $\mathbb{Q}_q$ inside the algebraic closure $\Omega =$ `PadicAlgCl q`, together with a monoid homomorphism $r : \mathrm{Gal}(\Omega/K) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ satisfying the hypothesis `hlevel`: for every intermediate field $E$ of $\Omega/K$ finite over $K$ there is a finite extension $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ with $r\sigma$ fixing $F$ pointwise already fixes $E$ pointwise. Let $N > 0$ and put $L = K(\{\zeta : \zeta^{q^N-1} = 1\})$, assumed finite and normal over $K$; let $\varphi$ be a $K$-automorphism of $L$ all of whose powers exhaust $\mathrm{Gal}(L/K)$, and let $\pi \in L^{\times}$ be a unit whose underlying element lies in $K$. Write $c(\sigma,\tau)$ for the carry cochain `carryFun`, equal to $\pi$ (written additively) when $\log_\varphi \sigma + \log_\varphi \tau \ge \operatorname{ord}(\varphi)$ and $0$ otherwise, where $\log_\varphi$ takes values in $\{0,\dots,\operatorname{ord}(\varphi)-1\}$; assume $c$ is a $2$-cocycle for `Rep.ofAlgebraAutOnUnits K L`. Finally let $E$ be an intermediate field of $\Omega/K$, finite over $K$, with $[L:K] \mid [E:K]$. Then the inflation `unitsInflate₂ L c`, pulled back along the inclusion $\mathrm{Gal}(\Omega/E) \cong E.\mathrm{fixingSubgroup} \hookrightarrow \mathrm{Gal}(\Omega/K)$ in both arguments, lies in `levelCoboundaries₂` for the composite level map $r$ restricted to $\mathrm{Gal}(\Omega/E)$ and the representation `Rep.ofAlgebraAutOnUnits E Ω`.
--
--   This is the statement that the inflated unramified class of degree $[L:K]$ attached to $\pi$ dies, as a level class, over any finite extension $E/K$ whose degree is divisible by $[L:K]$; it is obtained by rewriting the restriction of the $K$-inflation as the $E$-inflation of the transported cocycle, showing that the latter is a coboundary over $E$, and inflating. It is used in [`groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic`](thm.html#groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic), in the local analysis of degree-two level cohomology of the multiplicative group over $p$-adic fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology

theorem groupCohomology.unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (φ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (hφ : ∀ σ, σ ∈ Subgroup.zpowers φ)
    (π : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) (hπK : ((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) ∈ (K : Set (PadicAlgCl q)))
    (hcoc : carryFun φ hφ (isOfFinOrder_of_finite φ) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π)
      ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E]
    (hdvd : Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∣ Module.finrank K E) :
    (fun g : (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) =>
        unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
          (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π))
          ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.1, (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.2))
      ∈ levelCoboundaries₂ (r.comp (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom)) (Rep.ofAlgebraAutOnUnits E (PadicAlgCl q)) := by sorry
