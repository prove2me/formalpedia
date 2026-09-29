-- Prove2me | solution 1 for BallaEquiangular.tsq_inner
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:45:22.242908+00:00
-- url     : https://prove2.me/submissions/a5281903-3690-47a4-a0fe-2b5d035e7c11

-- Sol generated from Geometry/AbstractAlgebra/BallaEquiangular.lean
import Mathlib
import Definitions.Def_Geometry_AbstractAlgebra_BallaEquiangular
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Balla's bound `N ≤ d²` for equiangular line systems

A family of `N` unit vectors in `ℝ^d` is *equiangular* with common angle `α` when
`|⟨vᵢ, vⱼ⟩| = α` for all `i ≠ j`.  This file proves the classical bound that such a
family can have at most `d²` members.

The argument is the **tensor-square lift**.  To each unit vector `v ∈ ℝ^d` we
associate its tensor square `tsq v ∈ ℝ^{d²}`, whose coordinates are the products
`vₐ·v_b`.  The fundamental property is
`⟨tsq u, tsq v⟩ = ⟨u, v⟩²` (`tsq_inner`),
so the Gram matrix of the lifted vectors has constant diagonal `1` and constant
off-diagonal `α²`.

Rather than diagonalising this Gram matrix, we use the elementary **quadratic-form
identity** for constant-pattern matrices
`∑ᵢⱼ xᵢ Gᵢⱼ xⱼ = (1 - c)·∑ᵢ xᵢ² + c·(∑ᵢ xᵢ)²`  (`constPattern_quadForm`),
from which positive-definiteness (`constPattern_posDef`) is immediate when
`0 ≤ c < 1`.  Positive-definiteness of the Gram form forces the lifted vectors to be
linearly independent, and the rank bound in `ℝ^{d²}` yields `N ≤ d²`.
-/

open scoped RealInnerProductSpace

open BallaEquiangular

variable {d : ℕ}



/-! ## Stage 1 — The tensor-square inner product -/



/-! ## Stage 2 — Off-diagonal Gram entries -/


/-! ## Stage 3 — Quadratic form of constant-pattern matrices -/



/-! ## Stage 4 — Balla's bound -/



open BallaEquiangular in
theorem solution(u v : EuclideanSpace ℝ (Fin d)) : ⟪tsq u, tsq v⟫ = ⟪u, v⟫ ^ 2 := by
  have hinner : ∀ (x y : EuclideanSpace ℝ (Fin d)), ⟪x, y⟫ = ∑ i, x i * y i := by
    intro x y; rw [PiLp.inner_apply]; simp [mul_comm]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hinner u v, sq, Finset.sum_mul_sum]
  rw [← finProdFinEquiv.sum_comp (fun p => (tsq v) p * (tsq u) p)]
  rw [Fintype.sum_prod_type]
  congr 1; ext a; congr 1; ext b
  show tsq v (finProdFinEquiv (a, b)) * tsq u (finProdFinEquiv (a, b)) = _
  simp only [tsq, WithLp.equiv_symm_apply, Equiv.symm_apply_apply]
  ring
