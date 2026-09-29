-- Prove2me | solution 1 for BallaEquiangular.constPattern_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:45:21.613505+00:00
-- url     : https://prove2.me/submissions/6d254c52-1614-4b1f-b551-5bed37ecb431

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
theorem solution{N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → G i j = c) (x : Fin N → ℝ) :
    ∑ i, ∑ j, x i * G i j * x j = (1 - c) * ∑ i, (x i) ^ 2 + c * (∑ i, x i) ^ 2 := by
  have hG : ∀ i j, G i j = c + (if i = j then (1 - c) else 0) := by
    intro i j
    by_cases h : i = j
    · subst h; simp [hdiag i]
    · simp [h, hoff i j h]
  have step1 : ∑ i, ∑ j, x i * G i j * x j
      = ∑ i, ∑ j, (c * (x i * x j) + (if i = j then (1 - c) else 0) * (x i * x j)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hG i j]; ring
  rw [step1]
  simp only [Finset.sum_add_distrib]
  have A : ∑ i, ∑ j, c * (x i * x j) = c * (∑ i, x i) ^ 2 := by
    have h : ∑ i, ∑ j, c * (x i * x j) = c * ∑ i, ∑ j, x i * x j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    rw [h, sq, Finset.sum_mul_sum]
  have B : ∑ i, ∑ j, (if i = j then (1 - c) else 0) * (x i * x j) = (1 - c) * ∑ i, (x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_eq_single i]
    · simp [sq, mul_comm, mul_assoc]
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [A, B]; ring
