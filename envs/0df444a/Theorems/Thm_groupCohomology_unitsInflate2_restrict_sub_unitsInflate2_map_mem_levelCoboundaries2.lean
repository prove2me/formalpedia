-- Prove2me | Theorems.Thm_groupCohomology_unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2
-- name    : groupCohomology.unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/dcd04ea2-6776-5199-9551-d7c835230ae3
-- title:
--   Inflation from K(μ_{q^N-1}) restricts to inflation from E(μ_{q^N-1})
-- statement:
--   Fix a prime $q$, write $\Omega =$ `PadicAlgCl q` for the chosen algebraic closure of $\mathbb{Q}_q$, let $K$ be an intermediate field of $\mathbb{Q}_q \subseteq \Omega$ and $r$ a monoid homomorphism from $\mathrm{Gal}(\Omega/K)$ to $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ (the level map), let $E$ be an intermediate field of $K \subseteq \Omega$ and $N$ a natural number. Put $K_N = K(\{\zeta \in \Omega : \zeta^{q^N-1} = 1\})$ and $E_N = E(\{\zeta \in \Omega : \zeta^{q^N-1} = 1\})$, assumed normal over $K$ and over $E$ respectively. Given a monoid homomorphism $j : \mathrm{Gal}(E_N/E) \to \mathrm{Gal}(K_N/K)$ which, by hypothesis `hj`, satisfies $(j\sigma)(x) = \sigma(y)$ in $\Omega$ whenever $x \in K_N$ and $y \in E_N$ have the same image in $\Omega$; a morphism $\psi$ from the representation `Rep.ofAlgebraAutOnUnits K K_N` (the $\mathrm{Gal}(K_N/K)$-module $\mathrm{Additive}\,K_N^{\times}$) restricted along $j$ to `Rep.ofAlgebraAutOnUnits E E_N`, which by hypothesis `hψ` is the inclusion on underlying elements of $\Omega$; and an arbitrary function $f$ on pairs of elements of $\mathrm{Gal}(K_N/K)$ with values in $\mathrm{Additive}\,K_N^{\times}$ (no cocycle condition is imposed). Let $\iota : \mathrm{Gal}(\Omega/E) \to \mathrm{Gal}(\Omega/K)$ be the inverse of `IntermediateField.fixingSubgroupEquiv` followed by the inclusion of the fixing subgroup of $E$. Then the function on pairs $(g_1,g_2)$ of elements of $\mathrm{Gal}(\Omega/E)$ given by $\mathtt{unitsInflate₂}\,K_N\,f\,(\iota g_1, \iota g_2)$ minus $\mathtt{unitsInflate₂}\,E_N\,(p \mapsto \psi(f(j p_1, j p_2)))\,(g_1,g_2)$ lies in the submodule $\mathtt{levelCoboundaries₂}$ for the level map $r \circ \iota$ and the $\mathrm{Gal}(\Omega/E)$-module $\mathrm{Additive}\,\Omega^{\times}$.
--
--   This is the compatibility of the two unit-valued inflation maps from the cyclotomic layers $K_N$ and $E_N$ with restriction from $\mathrm{Gal}(\Omega/K)$ to $\mathrm{Gal}(\Omega/E)$, stated in the form needed for the continuous $H^2$ formalism with a level map. It is the bookkeeping half of the statement that the class of the unramified generator of degree $m$ becomes trivial over any $E$ with $m \mid [E:K]$, and is used by [`groupCohomology.unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd`](thm.html#groupCohomology.unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q))
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (E : IntermediateField K (PadicAlgCl q))
    (N : ℕ)
    [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (j : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) →* ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (hj : ∀ (σ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})),
      (x : PadicAlgCl q) = (y : PadicAlgCl q) → ((j σ x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ((σ y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (ψ : Rep.res j (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ⟶ Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
    (hψ : ∀ u : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ,
      (((Additive.toMul (ψ.hom (Additive.ofMul u)) : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q)
        = ((u : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q))
    (f : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) × ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) → Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) :
    (fun g : (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) =>
        unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.1, (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.2)
        - unitsInflate₂ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (fun p => ψ.hom (f (j p.1, j p.2))) g)
      ∈ levelCoboundaries₂ (r.comp (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom)) (Rep.ofAlgebraAutOnUnits E (PadicAlgCl q)) := by sorry
