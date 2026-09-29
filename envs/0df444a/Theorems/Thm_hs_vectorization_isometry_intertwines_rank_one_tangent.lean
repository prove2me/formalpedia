-- Prove2me | Theorems.Thm_hs_vectorization_isometry_intertwines_rank_one_tangent
-- name    : hs_vectorization_isometry_intertwines_rank_one_tangent
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-24T01:39:18.318447+00:00
-- url     : https://prove2.me/theorems/85e938fa-86c6-43cb-acbd-5893819950e3
-- statement:
--   The Hilbert-Schmidt vectorization $\mathrm{vec}(X)_{(a,b)} = X_{ab}$ flattening an $n_1\times n_2$ matrix to a vector indexed by coordinate pairs is a Frobenius-to-Euclidean isometry, and it intertwines each rank-one tangent operator with bot6 vecMulVec rank-one matrix. Concretely the theorem asserts three facts. (A) The Frobenius inner product equals the dot product of vectorizations: $\langle X,Y\rangle_F = \mathrm{vec}(X)\cdot\mathrm{vec}(Y)$. (B) The squared Frobenius norm equals the self dot product of the vectorization. (C) For $y_{ab} = P_T(e_a e_b^*) = \mathrm{tangentProjection}\,S\,(\mathrm{coordinateMatrix}\,a\,b)$, applying the matrix $\mathrm{vecMulVec}(\mathrm{vec}\,y_{ab})(\mathrm{vec}\,y_{ab})$ to $\mathrm{vec}(H)$ equals $\langle y_{ab},H\rangle_F\cdot\mathrm{vec}(y_{ab})$, i.e. the rank-one Hilbert-Schmidt operator $H\mapsto\langle y_{ab},H\rangle_F\,y_{ab}$ (the Rudelson summand $y_{ab}\otimes y_{ab}$) vectorizes to vecMulVec. This is the linchpin that brings the rank-one tensor-operator primitives and the matrix Khintchine / symmetrization machinery to bear on the Candes-Recht tangent sampling deviation.
-- source:
--   Rudelson, J. Funct. Anal. 164 (1999) Thm 1; van Handel, Structured Random Matrices arXiv:1610.05200 §3; Candes-Recht 2009 arXiv:0805.4471 §4.2

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Matrix

theorem hs_vectorization_isometry_intertwines_rank_one_tangent
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) :
    (∀ X Y : RealMatrix n1 n2,
        matrixInner X Y
          = (fun e : Fin n1 × Fin n2 => X e.1 e.2)
              ⬝ᵥ (fun e : Fin n1 × Fin n2 => Y e.1 e.2)) ∧
    (∀ X : RealMatrix n1 n2,
        frobeniusNormSq X
          = (fun e : Fin n1 × Fin n2 => X e.1 e.2)
              ⬝ᵥ (fun e : Fin n1 × Fin n2 => X e.1 e.2)) ∧
    (∀ (a : Fin n1) (b : Fin n2) (H : RealMatrix n1 n2),
        (Matrix.vecMulVec
            (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix a b) e.1 e.2)
            (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix a b) e.1 e.2)).mulVec
          (fun e : Fin n1 × Fin n2 => H e.1 e.2)
          = (matrixInner (tangentProjection S (coordinateMatrix a b)) H)
              • (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix a b) e.1 e.2)) := by sorry
