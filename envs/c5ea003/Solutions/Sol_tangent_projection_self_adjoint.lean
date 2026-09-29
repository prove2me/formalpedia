-- Prove2me | solution 1 for tangent_projection_self_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-24T03:12:48.376303+00:00
-- url     : https://prove2.me/submissions/1fafc0df-d369-4ed6-96e9-2c7eb6c194d2

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

/-
Self-adjointness (symmetry under the Frobenius inner product) of the tangent
projection `P_T = leftSingularProjection + rightSingularProjection -
twoSidedSingularProjection`:

    ⟨P_T A, B⟩_F = ⟨A, P_T B⟩_F  for all real matrices A, B.

This is the basic orthogonal-projection property the Candès–Recht tangent-space
analysis (arXiv:0805.4471 §3–§4) uses repeatedly: it underlies the
resolution-of-identity `X = ∑_{ab} ⟨P_T(e_ab), X⟩ P_T(e_ab)` for `X ∈ T`, and
the rank-one frame representation of the sampling fluctuation `P_T P_Ω P_T - p P_T`
used in the Rudelson selection lemma (Rudelson 1999, J. Funct. Anal. 164, Thm 1).

Proof: each of the three constituent projections is self-adjoint because its
kernel is symmetric (`∑_k u_k i u_k a` and `∑_l v_l b v_l j`).  The two-sided
projection equals `left ∘ right = right ∘ left`, so its self-adjointness follows
from composing the two self-adjoint factors.  matrixInner is bilinear, so
self-adjointness distributes over the `+`/`-`.  Uses only the SVD orthonormality
data implicitly (in fact only symmetry of the kernels, not orthonormality).
-/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    matrixInner (tangentProjection S A) B
      = matrixInner A (tangentProjection S B) := by
  -- inline helpers ----------------------------------------------------------
  -- kernel symmetry
  have PuK_symm_inline : ∀ (i a : Fin n1),
      (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    intro i a; apply Finset.sum_congr rfl; intro k _; ring
  have PvK_symm_inline : ∀ (b j : Fin n2),
      (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    intro b j; apply Finset.sum_congr rfl; intro l _; ring
  -- matrixInner bilinearity
  have matrixInner_add_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P + Q) C = matrixInner P C + matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [add_mul]
  have matrixInner_sub_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P - Q) C = matrixInner P C - matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [sub_mul]
  have matrixInner_add_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q + C) = matrixInner P Q + matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_add]
  have matrixInner_sub_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q - C) = matrixInner P Q - matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_sub]
  -- left self-adjoint
  have left_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (leftSingularProjection S P) Q
        = matrixInner P (leftSingularProjection S Q) := by
    intro P Q; unfold matrixInner leftSingularProjection
    rw [show (∑ i, ∑ j, (∑ a, (∑ k, S.u k i * S.u k a) * P a j) * Q i j)
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * P a j * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ a, (∑ k, S.u k i * S.u k a) * Q a j))
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * Q a j * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _; ring]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    rw [PuK_symm_inline i a]; ring
  -- right self-adjoint
  have right_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (rightSingularProjection S P) Q
        = matrixInner P (rightSingularProjection S Q) := by
    intro P Q; unfold matrixInner rightSingularProjection
    rw [show (∑ i, ∑ j, (∑ b, P i b * (∑ l, S.v l b * S.v l j)) * Q i j)
          = ∑ i, ∑ j, ∑ b, P i b * (∑ l, S.v l b * S.v l j) * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ b, Q i b * (∑ l, S.v l b * S.v l j)))
          = ∑ i, ∑ j, ∑ b, Q i b * (∑ l, S.v l b * S.v l j) * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    rw [PvK_symm_inline b j]; ring
  -- twoSided = left ∘ right and = right ∘ left
  have ts_lr : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = leftSingularProjection S (rightSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ a, (∑ k, S.u k i * S.u k a) * (∑ b, X a b * (∑ l, S.v l b * S.v l j)))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
  have ts_rl : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = rightSingularProjection S (leftSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
                = ∑ b, ∑ a, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
                apply Finset.sum_congr rfl; intro b _
                rw [Finset.sum_mul]]
          rw [Finset.sum_comm]]
  -- twoSided self-adjoint via composition
  have ts_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (twoSidedSingularProjection S P) Q
        = matrixInner P (twoSidedSingularProjection S Q) := by
    intro P Q
    rw [ts_lr, left_sa, right_sa, ← ts_rl]
  -- assemble
  unfold tangentProjection
  rw [matrixInner_sub_left, matrixInner_add_left, left_sa, right_sa, ts_sa,
      matrixInner_sub_right, matrixInner_add_right]
