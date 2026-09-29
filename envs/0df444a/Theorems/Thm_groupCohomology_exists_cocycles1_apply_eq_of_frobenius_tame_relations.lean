-- Prove2me | Theorems.Thm_groupCohomology_exists_cocycles1_apply_eq_of_frobenius_tame_relations
-- name    : groupCohomology.exists_cocycles1_apply_eq_of_frobenius_tame_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/63495044-e960-5c17-b8a5-8c7aaab0d81e
-- title:
--   Extending a value on the tame generator to a 1-cocycle
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $A$ a $k$-linear representation of $G$ with action map $\rho$. Fix elements $t,\varphi\in G$ and natural numbers $m$, $fo$, $jo$ subject to: $\varphi^{-1}t\varphi=t^{m}$; $\varphi^{fo}=t^{jo}$; the minimality condition that $fo$ divides every natural number $d$ with $\varphi^{d}$ lying in the subgroup of integral powers of $t$; and the generation condition that every $x\in G$ can be written as $\varphi^{a}t^{b}$ with $a,b$ natural numbers. Assume moreover that the endomorphism $\sum_{i<fo}\rho(\varphi^{i})$ of $A$ vanishes. Finally let $v,w\in A$ satisfy the three conditions $\sum_{i<\operatorname{ord}(t)}\rho(t^{i})v=0$, $\sum_{i<jo}\rho(t^{i})v=0$ and $$\rho(t)w-w=\rho(\varphi)\Bigl(\sum_{i<m}\rho(t^{i})v\Bigr)-v.$$ The conclusion is that there exists a $1$-cocycle $c$ of $G$ with values in $A$ (an element of `cocycles₁ A`) whose value at $t$ is $v$.
--
--   This is the cocycle-level construction underlying the inequality in one direction of the local Euler characteristic computation for a finite Galois group at a prime $\ell$ different from the residue characteristic, presented with $t$ a tame generator and $\varphi$ a Frobenius lift satisfying $\varphi^{-1}t\varphi=t^{m}$ and $\varphi^{fo}=t^{jo}$. It is used by [`groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth`](thm.html#groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth) to bound the dimension of $H^1$ from below.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_cocycles1_apply_eq_of_frobenius_tame_relations.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.exists_cocycles1_apply_eq_of_frobenius_tame_relations {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
    (t φ : G) (m fo jo : ℕ)
    (hm : φ⁻¹ * t * φ = t ^ m)
    (hrel : φ ^ fo = t ^ jo) (hmin : ∀ d : ℕ, φ ^ d ∈ Subgroup.zpowers t → fo ∣ d)
    (hgen : ∀ x : G, ∃ a b : ℕ, x = φ ^ a * t ^ b)
    (hNφ : ∑ i ∈ Finset.range fo, A.ρ (φ ^ i) = 0)
    (v w : A)
    (hNe : ∑ i ∈ Finset.range (orderOf t), A.ρ (t ^ i) v = 0)
    (hNj : ∑ i ∈ Finset.range jo, A.ρ (t ^ i) v = 0)
    (hw : A.ρ t w - w = A.ρ φ (∑ i ∈ Finset.range m, A.ρ (t ^ i) v) - v) :
    ∃ c : cocycles₁ A, c t = v := by sorry
