-- Prove2me | Theorems.Thm_RHLinalg_rank_specMap
-- name    : RHLinalg.rank_specMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:37:57.166344+00:00
-- url     : https://prove2.me/theorems/6709bebd-5ae0-473f-8815-0d673f0000b4
-- title:
--   Rank of a spectral function of a Hermitian matrix: $\operatorname{rank} f(A) = \#\{i : f(\lambda_i) \ne 0\}$
-- statement:
--   Let $A$ be an $n \times n$ Hermitian matrix over an `RCLike` field with eigenvalues $\lambda_1, \dots, \lambda_n$, and for $f : \mathbb{R} \to \mathbb{R}$ let $\operatorname{specMap}(A, f) = U \operatorname{diag}(f(\lambda_i)) U^{\mathsf H}$ be the spectral functional calculus applied to $A$.
--
--   **Statement.**
--   $$\operatorname{rank}\bigl(\operatorname{specMap}(A, f)\bigr) \;=\; \#\{\, i \;:\; f(\lambda_i) \ne 0 \,\},$$
--   the number of indices at which $f$ does not annihilate the corresponding eigenvalue.
--
--   Since conjugation by the unitary $U$ preserves rank, this reduces to the rank of a diagonal matrix. In the module `Zeta23.LinAlg.HermitianPosPart` this bookkeeping identity is used pervasively across the linear-algebra layer: it feeds `RHLinalg.finrank_le_posIndex_of_posDefOn`, `RHLinalg.posIndex_add_le`, `RHLinalg.rank_trace_ineq`, and the zero-side estimates `Zeta23.ZeroSide.ZeroBlockData.posIndex_blockA_le`, `posIndex_blockQ_le`, and `Zeta23.ZeroSide.posIndex_smul_pos` — in particular identifying the rank of the positive part $A_+$ with the positive index $n_+(A)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/HermitianPosPart.lean#L117-L131

import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex

open Matrix Finset Unitary
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.rank_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (specMap hA f).rank = #{i | f (hA.eigenvalues i) ≠ 0} := by sorry
