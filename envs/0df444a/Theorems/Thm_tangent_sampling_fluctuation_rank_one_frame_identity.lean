-- Prove2me | Theorems.Thm_tangent_sampling_fluctuation_rank_one_frame_identity
-- name    : tangent_sampling_fluctuation_rank_one_frame_identity
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-24T03:14:24.600538+00:00
-- url     : https://prove2.me/theorems/18f5200d-412c-408e-8996-fe0d92a5fb98
-- statement:
--   Rank-one frame representation of the un-normalised tangent sampling fluctuation. For a matrix $X$ in the tangent space $T$ (i.e. $P_T X = X$), the operator $P_T(P_\Omega X) - p\,X$ equals the rank-one tensor sum $\sum_{(a,b)} (\delta_{ab}-p)\,X_{ab}\,y_{ab}$, where $\delta_{ab}=[(a,b)\in\Omega]$ is the sampling indicator, $p$ the sampling probability, and $y_{ab}=P_T(e_ae_b^*)=$ $\texttt{tangentProjection } S\,(\texttt{coordinateMatrix } a\,b)$ the projected coordinate frame. Proof: $P_\Omega X=\sum_{ab}\delta_{ab}X_{ab}e_{ab}$, and for $X\in T$ the resolution of identity $X=\sum_{ab}X_{ab}y_{ab}$ holds (apply $P_T$ to the standard coordinate decomposition); applying $P_T$ to the sampled matrix by linearity/homogeneity and subtracting $p\,X$ gives the claimed sum. Combined with the Hilbert-Schmidt vectorization (each summand $X_{ab}\,y_{ab}$ becomes $(\texttt{vecMulVec}(\text{vec }y_{ab})(\text{vec }y_{ab})).\texttt{mulVec}(\text{vec }X)$), this exhibits the fluctuation as the rank-one tensor sum $\sum (\delta_{ab}-p)\,y_{ab}\otimes y_{ab}$ whose operator norm is the Rudelson-selection deviation $Z$. This is the operator-sum representation that lets the general matrix non-commutative Khintchine engine plus the Loewner collapse be instantiated with $H_{ab}=y_{ab}\otimes y_{ab}$.
-- source:
--   Candes-Recht arXiv:0805.4471 §3-§4.2; Rudelson 1999 J. Funct. Anal. 164 Thm 1

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Matrix

theorem tangent_sampling_fluctuation_rank_one_frame_identity
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    tangentProjection S (samplingProjection Omega X) - p • X
      = ∑ ab : Fin n1 × Fin n2,
          (((if ab ∈ Omega then (1:Real) else 0) - p) * X ab.1 ab.2)
            • tangentProjection S (coordinateMatrix ab.1 ab.2) := by sorry
