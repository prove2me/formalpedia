-- Prove2me | solution 1 for tangent_projection_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:31:30.289454+00:00
-- url     : https://prove2.me/submissions/a31ea902-e3f4-4a8b-b034-4548ed9b089d

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- The column singular kernel collapses: `∑_a K_U(i,a) K_U(a,a') = K_U(i,a')`,
    where `K_U(i,a) = ∑_k u_k i * u_k a`. This is `P_U² = P_U` at kernel level. -/
private lemma KU_collapse (S : SVD M r) (i a' : Fin n1) :
    (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
        (∑ k' : Fin r, S.u k' a * S.u k' a'))
      = ∑ k : Fin r, S.u k i * S.u k a' := by
  calc ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')
      = ∑ a : Fin n1, ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k a) * (S.u k' a * S.u k' a') := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul_sum]
    _ = ∑ k : Fin r, ∑ k' : Fin r, ∑ a : Fin n1,
          (S.u k i * S.u k a) * (S.u k' a * S.u k' a') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k' a') * (∑ a : Fin n1, S.u k a * S.u k' a) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k' a') * (if k = k' then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [S.u_orthonormal k k']
    _ = ∑ k : Fin r, S.u k i * S.u k a' := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (∑ k' : Fin r, S.u k i * S.u k' a' * if k = k' then 1 else 0)
            = ∑ k' : Fin r, if k = k' then S.u k i * S.u k' a' else 0 from by
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          by_cases h : k = k' <;> simp [h]]
        rw [Finset.sum_ite_eq Finset.univ k (fun k' => S.u k i * S.u k' a')]
        simp

/-- The row singular kernel collapses: `∑_b K_V(b',b) K_V(b,j) = K_V(b',j)`. -/
private lemma KV_collapse (S : SVD M r) (b' j : Fin n2) :
    (∑ b : Fin n2, (∑ k : Fin r, S.v k b' * S.v k b) *
        (∑ k' : Fin r, S.v k' b * S.v k' j))
      = ∑ k : Fin r, S.v k b' * S.v k j := by
  calc ∑ b : Fin n2, (∑ k : Fin r, S.v k b' * S.v k b) *
          (∑ k' : Fin r, S.v k' b * S.v k' j)
      = ∑ b : Fin n2, ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k b) * (S.v k' b * S.v k' j) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.sum_mul_sum]
    _ = ∑ k : Fin r, ∑ k' : Fin r, ∑ b : Fin n2,
          (S.v k b' * S.v k b) * (S.v k' b * S.v k' j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k' j) * (∑ b : Fin n2, S.v k b * S.v k' b) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k' j) * (if k = k' then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [S.v_orthonormal k k']
    _ = ∑ k : Fin r, S.v k b' * S.v k j := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (∑ k' : Fin r, S.v k b' * S.v k' j * if k = k' then 1 else 0)
            = ∑ k' : Fin r, if k = k' then S.v k b' * S.v k' j else 0 from by
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          by_cases h : k = k' <;> simp [h]]
        rw [Finset.sum_ite_eq Finset.univ k (fun k' => S.v k b' * S.v k' j)]
        simp

/-- `P_U` is idempotent. -/
private lemma left_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X)
      = leftSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection]
  rw [show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
        ∑ a' : Fin n1, (∑ k' : Fin r, S.u k' a * S.u k' a') * X a' j)
      = ∑ a : Fin n1, ∑ a' : Fin n1,
          ((∑ k : Fin r, S.u k i * S.u k a) *
            (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    ring]
  rw [Finset.sum_comm]
  rw [show (∑ a' : Fin n1, ∑ a : Fin n1,
        ((∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j)
      = ∑ a' : Fin n1, (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j from by
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [KU_collapse S i a']

/-- `P_V` is idempotent. -/
private lemma right_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X)
      = rightSingularProjection S X := by
  funext i j
  simp only [rightSingularProjection]
  rw [show (∑ b : Fin n2, (∑ b' : Fin n2, X i b' * (∑ k : Fin r, S.v k b' * S.v k b)) *
        (∑ k' : Fin r, S.v k' b * S.v k' j))
      = ∑ b' : Fin n2, X i b' * (∑ b : Fin n2,
          (∑ k : Fin r, S.v k b' * S.v k b) * (∑ k' : Fin r, S.v k' b * S.v k' j))
        from by
    rw [show (∑ b : Fin n2, (∑ b' : Fin n2, X i b' * (∑ k : Fin r, S.v k b' * S.v k b)) *
          (∑ k' : Fin r, S.v k' b * S.v k' j))
        = ∑ b : Fin n2, ∑ b' : Fin n2,
            X i b' * ((∑ k : Fin r, S.v k b' * S.v k b) *
              (∑ k' : Fin r, S.v k' b * S.v k' j)) from by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      ring]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  rw [KV_collapse S b' j]

/-- `P_U` and `P_V` commute, and the composite is `twoSided`:
    `P_U (P_V X) = twoSided X`. -/
private lemma left_right_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]
  -- LHS: ∑ a, KU(i,a) * (∑ b, X a b * KV(b,j))
  -- RHS: ∑ a, ∑ b, KU(i,a) * X a b * KV(b,j)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `P_V (P_U X) = twoSided X` (the other composition order). -/
private lemma right_left_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]
  -- LHS: ∑ b, (∑ a, KU(i,a) * X a b) * KV(b,j)
  -- RHS: ∑ a, ∑ b, KU(i,a) * X a b * KV(b,j)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

/-- `P_U (twoSided X) = twoSided X`: applying `P_U` again is idempotent. -/
private lemma left_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, twoSidedSingularProjection]
  -- LHS: ∑ a', KU(i,a') * (∑ a ∑ b, KU(a',a) X a b KV(b,j))
  -- RHS: ∑ a ∑ b, KU(i,a) X a b KV(b,j)
  -- collapse over a': coefficient of (X a b * KV(b,j)) is ∑ a' KU(i,a') KU(a',a) = KU(i,a)
  rw [show (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
        ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k' : Fin r, S.u k' a' * S.u k' a) * X a b *
            (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
            (∑ k' : Fin r, S.u k' a' * S.u k' a)) *
            (X a b * (∑ l : Fin r, S.v l b * S.v l j)) from by
    -- First: distribute KU(i,a') over the inner ∑a ∑b and turn LHS into a
    -- fully expanded triple sum over a', a, b.
    rw [show (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
          ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k' : Fin r, S.u k' a' * S.u k' a) * X a b *
              (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ a' : Fin n1, ∑ a : Fin n1, ∑ b : Fin n2,
            ((∑ k : Fin r, S.u k i * S.u k a') *
              (∑ k' : Fin r, S.u k' a' * S.u k' a)) *
              (X a b * (∑ l : Fin r, S.v l b * S.v l j)) from by
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    -- Move ∑ a' innermost: swap a' with a, then a' with b.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [KU_collapse S i a]
  ring

/-- `P_V (twoSided X) = twoSided X`. -/
private lemma right_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [rightSingularProjection, twoSidedSingularProjection]
  -- LHS: ∑ b', (∑ a ∑ b, KU(i,a) X a b KV(b,b')) * KV(b',j)
  -- RHS: ∑ a ∑ b, KU(i,a) X a b KV(b,j)
  rw [show (∑ b' : Fin n2, (∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k : Fin r, S.u k i * S.u k a) * X a b *
            (∑ l : Fin r, S.v l b * S.v l b')) *
        (∑ l' : Fin r, S.v l' b' * S.v l' j))
      = ∑ a : Fin n1, ∑ b : Fin n2,
          ((∑ k : Fin r, S.u k i * S.u k a) * X a b) *
            (∑ b' : Fin n2, (∑ l : Fin r, S.v l b * S.v l b') *
              (∑ l' : Fin r, S.v l' b' * S.v l' j)) from by
    -- First: distribute KV(b',j) over the inner ∑a ∑b and expand to a triple sum.
    rw [show (∑ b' : Fin n2, (∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k : Fin r, S.u k i * S.u k a) * X a b *
              (∑ l : Fin r, S.v l b * S.v l b')) *
          (∑ l' : Fin r, S.v l' b' * S.v l' j))
        = ∑ b' : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            ((∑ k : Fin r, S.u k i * S.u k a) * X a b) *
              ((∑ l : Fin r, S.v l b * S.v l b') *
                (∑ l' : Fin r, S.v l' b' * S.v l' j)) from by
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    -- Move ∑ b' innermost: swap b' with a, then b' with b.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [KV_collapse S b j]

/-- `twoSided = P_U ∘ P_V`. -/
private lemma two_eq_left_right (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X
      = leftSingularProjection S (rightSingularProjection S X) :=
  (left_right_eq_two S X).symm

/-- `twoSided (P_U X) = twoSided X`. -/
private lemma two_left_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_left_eq_two, left_two_eq_two]

/-- `twoSided (P_V X) = twoSided X`. -/
private lemma two_right_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_idem, left_right_eq_two]

/-- `twoSided (twoSided X) = twoSided X`. -/
private lemma two_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_two_eq_two, left_two_eq_two]

/-- `P_U` is additive. -/
private lemma left_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B)
      = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  simp only [leftSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- `P_V` is additive. -/
private lemma right_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B)
      = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  simp only [rightSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `twoSided` is additive. -/
private lemma two_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  simp only [twoSidedSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `P_U` respects subtraction. -/
private lemma left_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B)
      = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  simp only [leftSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- `P_V` respects subtraction. -/
private lemma right_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B)
      = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  simp only [rightSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `twoSided` respects subtraction. -/
private lemma two_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  simp only [twoSidedSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

end MatrixCompletion

theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  -- tangentProjection S Y = P_U Y + P_V Y - twoSided Y, and P_U, P_V, twoSided are
  -- additive.  Expand the outer projection over the inner +/-, then substitute the
  -- nine composition identities; the result telescopes by `abel`.
  simp only [tangentProjection]
  rw [left_sub, left_add, right_sub, right_add, two_sub, two_add,
    left_idem, right_idem, left_right_eq_two, right_left_eq_two,
    left_two_eq_two, right_two_eq_two,
    two_left_eq_two, two_right_eq_two, two_two_eq_two]
  abel
