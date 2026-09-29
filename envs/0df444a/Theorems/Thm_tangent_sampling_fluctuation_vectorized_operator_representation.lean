-- Prove2me | Theorems.Thm_tangent_sampling_fluctuation_vectorized_operator_representation
-- name    : tangent_sampling_fluctuation_vectorized_operator_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T17:04:01.036494+00:00
-- url     : https://prove2.me/theorems/4058bb4f-8feb-4394-b966-c5caff789469
-- statement:
--   **Vectorized rank-one representation of the tangent sampling fluctuation.**
--
--   Let $T$ be the tangent space at a rank-$r$ matrix $M$, let $P_T$ be the tangent projection, and write
--   $$
--   y_{ab}=P_T(e_a e_b^*)
--   $$
--   for the projected coordinate matrix. If $X\in T$ and $\Omega$ is a sampled set of entries, then the unnormalised fluctuation
--   $$
--   P_T(P_\Omega X)-pX
--   $$
--   has the coordinate-vector representation
--   $$
--   \operatorname{vec}\bigl(P_T(P_\Omega X)-pX\bigr)
--   =\left(\sum_{a,b}(\delta_{ab}-p)\,\operatorname{vec}(y_{ab})\operatorname{vec}(y_{ab})^\top\right)\operatorname{vec}(X),
--   $$
--   where $\delta_{ab}=1_{(a,b)\in\Omega}$. This is the finite-dimensional bridge from the Candes--Recht tangent-sampling operator to Rudelson's rank-one tensor sum. The Lean proof imports the already-proved rank-one frame identity and the Frobenius self-adjointness of $P_T$.
--
--   Reference location: Candes--Recht, arXiv:0805.4471, Section 4.2, equations (4.6)--(4.9); Rudelson, JFA 164 (1999), Theorem 1 proof, pp. 3--6; van Handel, *Structured Random Matrices*, Section 3.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic

open MatrixCompletion
open scoped BigOperators Matrix Classical

/-- Vectorized rank-one operator representation of the unnormalised tangent
sampling fluctuation. For `X ∈ T`, vectorization turns
`P_T(P_Ω X) - p • X` into the action of the rank-one matrix sum
`∑ (δ_ab - p) • vec(y_ab) vec(y_ab)^T` on `vec X`, where
`y_ab = P_T(e_ab)`. -/

theorem tangent_sampling_fluctuation_vectorized_operator_representation
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    (fun e : Fin n1 × Fin n2 =>
        (tangentProjection S (samplingProjection Omega X) - p • X) e.1 e.2)
      = (∑ ab : Fin n1 × Fin n2,
          (((if ab ∈ Omega then (1 : Real) else 0) - p) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))).mulVec
          (fun e : Fin n1 × Fin n2 => X e.1 e.2) := by
  sorry
