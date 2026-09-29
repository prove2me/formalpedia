-- Prove2me | solution 1 for BallaEquiangular.equiangular_card_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:48:00.509675+00:00
-- url     : https://prove2.me/submissions/ca8f6535-6a4d-49a1-962c-29e31caff340

-- Sol generated from Geometry/AbstractAlgebra/BallaEquiangular.lean
import Mathlib
import Definitions.Def_Geometry_AbstractAlgebra_BallaEquiangular
import Theorems.Thm_BallaEquiangular_constPattern_quadForm
import Theorems.Thm_BallaEquiangular_tsq_inner
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


/-- **Positive-definiteness of a constant-pattern matrix.**  If `G` has diagonal `1`
and off-diagonal `c` with `0 ≤ c < 1`, then its quadratic form is strictly positive
on nonzero vectors. -/
theorem constPattern_posDef {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → G i j = c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (x : Fin N → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, x i * G i j * x j := by
  rw [constPattern_quadForm G c hdiag hoff x]
  have hsum_pos : 0 < ∑ i, (x i) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    apply Finset.sum_pos'
    · intro j _; positivity
    · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have h1 : 0 < (1 - c) * ∑ i, (x i) ^ 2 := mul_pos (by linarith) hsum_pos
  have h2 : 0 ≤ c * (∑ i, x i) ^ 2 := by positivity
  linarith

/-! ## Stage 4 — Balla's bound -/



open BallaEquiangular in
theorem solution{N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin d))
    {α : ℝ} (hunit : ∀ i, ‖v i‖ = 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hang : ∀ i j, i ≠ j → |⟪v i, v j⟫| = α) : N ≤ d * d := by
  set w : Fin N → EuclideanSpace ℝ (Fin (d * d)) := fun i => tsq (v i) with hw
  set G : Matrix (Fin N) (Fin N) ℝ := fun i j => ⟪w i, w j⟫ with hG
  have hdiag : ∀ i, G i i = 1 := by
    intro i
    have hvi : ⟪v i, v i⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hunit i]; norm_num
    simp only [hG, hw, tsq_inner, hvi]; norm_num
  have hoff : ∀ i j, i ≠ j → G i j = α ^ 2 := by
    intro i j hij
    simp only [hG, hw, tsq_inner]
    rw [← hang i j hij, sq_abs]
  have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
  have hα2' : α ^ 2 < 1 := by nlinarith
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg0 : g = 0 := by
      by_contra hgne
      have hquad : ∑ i, ∑ j, g i * G i j * g j = 0 := by
        have expand : ⟪∑ i, g i • w i, ∑ j, g j • w j⟫ = ∑ i, ∑ j, g i * G i j * g j := by
          rw [sum_inner]
          apply Finset.sum_congr rfl; intro i _
          rw [inner_sum]
          apply Finset.sum_congr rfl; intro j _
          rw [real_inner_smul_left, real_inner_smul_right]; ring
        rw [← expand, hg, inner_zero_left]
      have := constPattern_posDef G (α ^ 2) hdiag hoff hα2 hα2' g hgne
      linarith
    exact fun i => congrFun hg0 i
  have hcard := hli.fintype_card_le_finrank
  simpa [finrank_euclideanSpace_fin] using hcard
