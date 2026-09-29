-- Prove2me | Theorems.Thm_ZLattice_exists_forall_ncard_add_mem_closedBall_le
-- name    : ZLattice.exists_forall_ncard_add_mem_closedBall_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c7d690b0-28cb-5171-b6d3-0adc33e8c6c9
-- title:
--   Uniform polynomial bound for lattice points in balls
-- statement:
--   Let $E$ be a finite-dimensional normed real vector space (a type carrying a normed additive commutative group structure, a real normed space structure and finite-dimensionality over $\mathbb{R}$), and let $L$ be an additive subgroup of $E$ whose subtype topology is discrete. The assertion is that there exists a real constant $C$ with $0 \le C$ such that for every $a \in E$ and every real $R \ge 0$ the set $\{x \in E : x \in L \text{ and } \lVert a + x\rVert \le R\}$ is finite and its cardinality, as a natural number cast to $\mathbb{R}$, satisfies $\#\{x \in L : \lVert a+x\rVert \le R\} \le C\,(1+R)^{\operatorname{finrank}_{\mathbb{R}} E}$. The constant is uniform in the centre: it depends only on $E$ and $L$, and not on $a$ or $R$. Note that the exponent is the dimension of the ambient space $E$, not the rank of $L$, and that $L$ is not required to span $E$; the counted set is the set of lattice points in the closed ball of radius $R$ centred at $-a$.
--
--   This is the standard uniform counting estimate for points of a discrete subgroup of a finite-dimensional real normed space in balls of radius $R$, as used in the geometry of numbers. It is applied in the proof of [`NumberField.exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow`](thm.html#NumberField.exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow), where the relevant lattice is a unit-logarithm lattice of a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZLattice_exists_forall_ncard_add_mem_closedBall_le.lean

import Mathlib.Algebra.Module.ZLattice.Summable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ZLattice.exists_forall_ncard_add_mem_closedBall_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (hL : DiscreteTopology L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E) (R : ℝ), 0 ≤ R →
      {x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.Finite ∧
      (({x : E | x ∈ L ∧ ‖a + x‖ ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ Module.finrank ℝ E := by sorry
