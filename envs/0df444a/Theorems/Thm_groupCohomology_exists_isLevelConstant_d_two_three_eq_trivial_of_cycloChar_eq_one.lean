-- Prove2me | Theorems.Thm_groupCohomology_exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one
-- name    : groupCohomology.exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/e799794a-6788-50b0-8584-ca3bb75c19ed
-- title:
--   Degree-three cochain exactness for ℤ/p over K supseteq μₚ
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $S$ be a finite set of rational primes containing $p$ (via `pPrime p`), and let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, which is unramified outside $S$ in the sense of `IsUnramifiedOutside`: $K$ is finite-dimensional over $\mathbb{Q}$ and for every rational prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ is contained in the fixing subgroup of $K$. Assume the mod-$p$ cyclotomic character `cycloChar p`, built from the modular cyclotomic character of $\overline{\mathbb{Q}}$, takes the value $1$ on every element of $K$'s fixing subgroup $\Gamma_K$. Let $u \colon \Gamma_K^3 \to \mathbb{Z}/p$ be a function valued in the trivial $\Gamma_K$-representation $\mathbb{Z}/p$ over $\mathbb{Z}/p$, which is level-constant outside $S$: there is an intermediate field $F$ unramified outside $S$ (in the same sense) with $u(g \cdot s) = u(g)$ for all $g, s \in \Gamma_K^3$ such that each component $s_i$ lies, as an automorphism of $\overline{\mathbb{Q}}$, in the fixing subgroup of $F$; and assume $u$ is a cocycle, i.e. the differential $d^{3,4}$ of the inhomogeneous cochain complex of the trivial representation annihilates $u$. Then there exists $w \colon \Gamma_K^2 \to \mathbb{Z}/p$, level-constant outside $S$ in the same sense (for some intermediate field unramified outside $S$), with $d^{2,3} w = u$.
--
--   This is the trivial-coefficient case, over a number field whose absolute Galois group acts trivially on $\mu_p$, of Tate's bound $\mathrm{cd}_p(G_{K,S}) \le 2$ for odd $p \in S$, phrased at the level of level-constant inhomogeneous cochains rather than as the vanishing of $H^3(G_{K,S}, \mathbb{Z}/p)$. It is used by [`groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two`](thm.html#groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two), the version for general smooth $\mathbb{F}_p$-coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_isLevelConstant_d_two_three_eq_trivial_of_cycloChar_eq_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥K]
    (hKζ : ∀ s ∈ K.fixingSubgroup, cycloChar p s = 1)
    (u : (Fin 3 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))
    (hlc : (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 3 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → u (g * s) = u g))
    (hcoc : ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 3 4).hom u = 0) :
    ∃ w : (Fin 2 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 2 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 2 3).hom w = u := by sorry
