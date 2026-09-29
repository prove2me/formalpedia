-- Prove2me | Theorems.Thm_Wolf_exists_pow_le_growthFunction_of_isPolycyclic_of_not_exists_nilpotent_finiteIndex
-- name    : Wolf.exists_pow_le_growthFunction_of_isPolycyclic_of_not_exists_nilpotent_finiteIndex
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T21:36:52.529797+00:00
-- url     : https://prove2.me/theorems/895d8f61-caa1-4e62-94b8-b34ee9d214f9
-- title:
--   Theorem 4.3 (2): a polycyclic group with no nilpotent subgroup of finite index grows at least exponentially
-- statement:
--   Let $\Gamma$ be a polycyclic group having **no** nilpotent subgroup of finite index,
--   and let $S$ be any finite generating set of $\Gamma$. Then there is a constant $v > 1$ such that
--   $v^m \le g_S(m)$ for every integer $m \ge 1$, where $g_S(m)$ is Wolf's growth function: the
--   number of elements of $\Gamma$ expressible as a product of at most $m$ factors drawn from
--   $S \cup S^{-1}$.
--
--   The constant is allowed to depend on $S$, and the conclusion is asserted for *every* finite
--   generating set. It gives exponential growth in the sense of the published growth bundle: at
--   $m = 0$ the ball is $\{1\}$ and $v^0 = 1$, so the restriction to $m \ge 1$ costs nothing, and
--   the single generating set that definition asks for can be taken to be any one of them.
--
--   The hypothesis is not vacuous, and it is strictly stronger than it may look. Taking the trivial
--   subgroup shows it forces $\Gamma$ to be infinite, and taking $\Gamma$ itself shows it forces
--   $\Gamma$ to be non-nilpotent; both are intended. Groups satisfying it exist — for instance
--   $\mathbb{Z}^2 \rtimes_A \mathbb{Z}$ for a hyperbolic $A \in SL_2(\mathbb{Z})$, which is
--   polycyclic and has no nilpotent subgroup of finite index.
--
--   The hypothesis is spelled out rather than named, but it is exactly Mathlib's
--   `Group.IsVirtuallyNilpotent` negated: that predicate is defined as the existence of a nilpotent
--   subgroup of finite index, with the same two conjuncts in the same order, so the two are the same
--   proposition by unfolding. It is written out here to match the form in which Wolf's Theorem 4.3
--   states it.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Theorem 4.3 (2), p. 434; proved on pp. 436–438 by way of Proposition 4.4

import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem exists_pow_le_growthFunction_of_isPolycyclic_of_not_exists_nilpotent_finiteIndex {Γ : Type*}
    [Group Γ] (h : MilnorWolf.IsPolycyclic Γ)
    (hno : ¬ ∃ Δ : Subgroup Γ, Group.IsNilpotent Δ ∧ Δ.FiniteIndex)
    (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    ∃ v : ℝ, 1 < v ∧ ∀ m : ℕ, 1 ≤ m → v ^ m ≤ (MilnorWolf.growthFunction S m : ℝ) := by
  sorry

end Wolf
