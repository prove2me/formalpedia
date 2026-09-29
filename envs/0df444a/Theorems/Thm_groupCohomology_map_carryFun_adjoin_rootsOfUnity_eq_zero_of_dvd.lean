-- Prove2me | Theorems.Thm_groupCohomology_map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd
-- name    : groupCohomology.map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/7bbc979c-b568-576b-8689-6c1615243c14
-- title:
--   Vanishing of the restricted carry class when [K_N:K]∣[E:K]
-- statement:
--   Fix a prime $q$ and work inside a fixed algebraic closure $\overline{\mathbb{Q}}_q$ = `PadicAlgCl q`. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$ finite over $\mathbb{Q}_q$, let $E$ be an intermediate field of $\overline{\mathbb{Q}}_q/K$ finite over $K$, and let $N>0$. Write $K_N$ and $E_N$ for the subfields generated over $K$, resp. over $E$, by $\{\zeta : \zeta^{q^N-1}=1\}$, assumed finite and normal over $K$, resp. over $E$. Let $\varphi_K \in \mathrm{Aut}_K(K_N)$ be such that every $K$-automorphism of $K_N$ lies in its cyclic subgroup of integral powers; let $j : \mathrm{Aut}_E(E_N) \to \mathrm{Aut}_K(K_N)$ be a group homomorphism such that for all $\sigma$ and all $x \in K_N$, $y \in E_N$ with the same image in $\overline{\mathbb{Q}}_q$, the elements $j(\sigma)(x)$ and $\sigma(y)$ again have the same image; and let $\psi$ be a morphism of $\mathbb{Z}$-linear representations from the restriction along $j$ of $K_N^\times$ (with its $\mathrm{Aut}_K(K_N)$-action, written additively) to $E_N^\times$, such that $\psi(u)$ and $u$ have the same image in $\overline{\mathbb{Q}}_q$ for every unit $u$ of $K_N$. Let $\pi$ be a unit of $K_N$ whose image lies in $K$, and consider the carry function of $\varphi_K$ at $\pi$: using the discrete logarithm $\ell$ sending $g$ to the element of $\{0,\dots,\mathrm{ord}(\varphi_K)-1\}$ with $\varphi_K^{\ell(g)}=g$, it sends $(g,h)$ to $\pi$ if $\mathrm{ord}(\varphi_K) \le \ell(g)+\ell(h)$ and to $0$ otherwise; it is assumed to be a $2$-cocycle. If $[K_N:K]$ divides $[E:K]$ (as ranks of $K$-modules), then the image of the class of this cocycle in $H^2(\mathrm{Aut}_K(K_N),K_N^\times)$ under the map induced by $(j,\psi)$ in degree $2$ is zero.
--
--   This is the cohomological half of the assertion that the carry class attached to the unramified-type cyclic extension $K(\mu_{q^N-1})/K$ and a uniformiser-like element $\pi$ of $K$ dies after restriction to $E$ as soon as the degree $[K(\mu_{q^N-1}):K]$ divides $[E:K]$, a local class field theory computation in the shape needed for the level bookkeeping. It is used by [`groupCohomology.unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd`](thm.html#groupCohomology.unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd.lean

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology

theorem groupCohomology.map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E]
    (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    [FiniteDimensional E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (φK : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (hφK : ∀ σ, σ ∈ Subgroup.zpowers φK)
    (j : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) →* ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (hj : ∀ (σ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})),
      (x : PadicAlgCl q) = (y : PadicAlgCl q) → ((j σ x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ((σ y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (ψ : Rep.res j (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ⟶ Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
    (hψ : ∀ u : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ,
      (((Additive.toMul (ψ.hom (Additive.ofMul u)) : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q)
        = ((u : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (π : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) (hπK : ((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) ∈ (K : Set (PadicAlgCl q)))
    (hcoc : carryFun φK hφK (isOfFinOrder_of_finite φK) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π)
      ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (hdvd : Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∣ Module.finrank K E) :
    (groupCohomology.map j ψ 2).hom
        ((H2π (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))).hom
          ⟨carryFun φK hφK (isOfFinOrder_of_finite φK) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π), hcoc⟩) = 0 := by sorry
