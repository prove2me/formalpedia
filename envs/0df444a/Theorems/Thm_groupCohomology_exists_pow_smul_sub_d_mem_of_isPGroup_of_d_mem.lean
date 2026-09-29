-- Prove2me | Theorems.Thm_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem
-- name    : groupCohomology.exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/3fd6a278-f816-5eb6-b496-0a2607575684
-- title:
--   Cochains mod W killed by p^k after a coboundary
-- statement:
--   Let $G$ be a finite group, $p$ a prime (registered as such), and suppose $G$ is a $p$-group in the sense of `IsPGroup p G`. Let $A$ be a $\mathbb{Z}$-linear representation of $G$ (an object of `Rep ℤ G` in the bottom universe), and let $W$ be an additive subgroup of $A$ which is stable under the action, i.e. $A.\rho(g)a \in W$ for every $g \in G$ and every $a \in W$, and which has finite index in $A$. Let $\nu$ be an inhomogeneous $1$-cochain, that is, a function $(\mathrm{Fin}\,1 \to G) \to A$, and assume that $\nu$ is a cocycle modulo $W$: the value of the differential $d^{1,2}$ of the inhomogeneous cochain complex `inhomogeneousCochains A` applied to $\nu$ lies in $W$ at every argument $(\mathrm{Fin}\,2 \to G)$. The conclusion asserts the existence of an inhomogeneous $0$-cochain $m \colon (\mathrm{Fin}\,0 \to G) \to A$ and a natural number $k$ such that for every $g \colon \mathrm{Fin}\,1 \to G$ one has $p^k \cdot \bigl(\nu(g) - (d^{0,1}m)(g)\bigr) \in W$, the scalar $p^k$ acting as an integer.
--
--   This is the cochain-level form of the elementary fact that, for a finite $p$-group acting on $A$ with a stable subgroup $W$ of finite index, the obstruction to correcting a cocycle-modulo-$W$ to a coboundary-modulo-$W$ is $p$-primary: the prime-to-$p$ part of the class of $\nu$ in $A/W$ is a coboundary. It is used in the construction of levels for $S$-idele coboundaries, via [`NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d`](thm.html#NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d), where the statement is consumed directly in the $\mathrm{Fin}$-indexed `inhomogeneousCochains` spelling.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_pow_smul_sub_d_mem_of_isPGroup_of_d_mem
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (A : Rep.{0} ℤ G) (W : AddSubgroup A) (hW : ∀ (g : G) (a : A), a ∈ W → A.ρ g a ∈ W) [W.FiniteIndex]
    (ν : (Fin 1 → G) → A)
    (hν : ∀ g : Fin 2 → G, ((inhomogeneousCochains A).d 1 2).hom ν g ∈ W) :
    ∃ (m : (Fin 0 → G) → A) (k : ℕ),
      ∀ g : Fin 1 → G, (p ^ k : ℤ) • (ν g - ((inhomogeneousCochains A).d 0 1).hom m g) ∈ W := by sorry
