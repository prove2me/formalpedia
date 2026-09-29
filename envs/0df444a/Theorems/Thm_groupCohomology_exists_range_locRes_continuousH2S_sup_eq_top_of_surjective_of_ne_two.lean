-- Prove2me | Theorems.Thm_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two
-- name    : groupCohomology.exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c75a4199-22f6-5945-8161-3057bc520206
-- title:
--   Dévissage of the degree-two localisation cokernel bound, odd p
-- statement:
--   Let $p$ be a prime, let $S$ be a finite set of primes, assume $p \neq 2$ and that $p$, viewed as an element of `Nat.Primes`, lies in $S$. Let $M_1$ and $M$ be representations of $\Gamma = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$, both finite-dimensional, and assume $M_1$ is smooth in the sense that every $m \in M_1$ is fixed by $\rho_{M_1}(s)$ for all $s$ in the fixing subgroup of some intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$. Let $\pi \colon M_1 \to M$ be a surjective $\mathbb{Z}/p$-linear map with $\pi(\rho_{M_1}(g)m) = \rho_M(g)\pi(m)$ for all $g \in \Gamma$, $m \in M_1$. For a representation $X$ of $\Gamma$ and a place index $v \in \mathrm{Unit} \sqcup S$, write $\mathrm{loc}_v$ for the map `locRes₂S` from the global group `continuousH2S S X` to `continuousH2` of $X$ restricted along `extArithLoc`, which for $v = \mathrm{inl}()$ is the inclusion of the decomposition group of complex conjugation `archimedeanDecomposition` into $\Gamma$ and for $v = \mathrm{inr}\,q$ is the map `primeLocalToGlobal` from the local Galois group at $q$ to $\Gamma$; here `continuousH2 r Y` is the quotient of `levelCocycles₂ r Y` by the coboundaries `levelCoboundaries₂ r Y` lying in it. Write $X^{\vee}(1) =$ `X.dualTwist (cycloChar p)` for the dual representation with its action multiplied by the mod-$p$ cyclotomic character $\Gamma \to (\mathbb{Z}/p)^{\times}$. The hypothesis is that for $M_1$ there is a $\mathbb{Z}/p$-submodule $W_1$ of $\prod_{q \in S}$ `continuousH2` at $q$ of $M_1$ which is finite over $\mathbb{Z}/p$, satisfies $\dim W_1 \le \dim (M_1^{\vee}(1))^{\Gamma}$, and is such that the image of $\ker \mathrm{loc}_{\mathrm{inl}()}$ under the product of the maps $\mathrm{loc}_{\mathrm{inr}\,q}$, $q \in S$, together with $W_1$ spans the whole product. The conclusion is the same assertion with $M_1$ replaced by $M$: there exists such a submodule $W$ of $\prod_{q \in S}$ `continuousH2` at $q$ of $M$, finite over $\mathbb{Z}/p$, with $\dim W \le \dim (M^{\vee}(1))^{\Gamma}$, whose sum with the image of $\ker \mathrm{loc}_{\mathrm{inl}()}$ under the product of the local restriction maps is everything.
--
--   This is the dévissage step in the existence half of the degree-two Poitou–Tate localisation statement: the bound on the cokernel of the localisation map on classes trivial at the archimedean place, with the bound expressed by the invariants of the Cartier dual, is transported along an equivariant surjection of smooth finite $\mathbb{F}_p$-representations of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, for odd $p$. It feeds the statement [`groupCohomology.exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two`](thm.html#groupCohomology.exists_range_locRes_continuousH2S_sup_eq_top_finrank_le_finrank_invariants_dualTwist_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_range_locRes_continuousH2S_sup_eq_top_of_surjective_of_ne_two
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2) (hpS : pPrime p ∈ S)
    (M₁ M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M₁] [FiniteDimensional (ZMod p) M]
    (hsm₁ : ∀ m : M₁, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M₁.ρ s m = m)
    (π : M₁ →ₗ[ZMod p] M) (hπ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M₁), π (M₁.ρ g m) = M.ρ g (π m))
    (hπs : Function.Surjective π)
    (h₁ : ∃ W₁ : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M₁)),
      Module.Finite (ZMod p) W₁ ∧
      Module.finrank (ZMod p) W₁ ≤ Module.finrank (ZMod p) (M₁.dualTwist (cycloChar p)).ρ.invariants ∧
      (LinearMap.ker (locRes₂S S M₁ (extArithLoc S (Sum.inl ())))).map
          (LinearMap.pi fun q : ↥S => locRes₂S S M₁ (extArithLoc S (Sum.inr q))) ⊔ W₁ = ⊤) :
    ∃ W : Submodule (ZMod p)
        (∀ q : ↥S, continuousH2 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M)),
      Module.Finite (ZMod p) W ∧
      Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (M.dualTwist (cycloChar p)).ρ.invariants ∧
      (LinearMap.ker (locRes₂S S M (extArithLoc S (Sum.inl ())))).map
          (LinearMap.pi fun q : ↥S => locRes₂S S M (extArithLoc S (Sum.inr q))) ⊔ W = ⊤ := by sorry
