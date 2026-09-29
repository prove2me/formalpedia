-- Prove2me | Theorems.Thm_RHLinalg_hermForm_specMap
-- name    : RHLinalg.hermForm_specMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:07.963549+00:00
-- url     : https://prove2.me/theorems/59cda321-2a6b-482c-b405-4338b1d4952e
-- title:
--   Hermitian form of a spectral function in eigenbasis coordinates: $\operatorname{Re}(x^{\mathsf H} f(A) x) = \sum_i f(\lambda_i)\|c_i\|^2$
-- statement:
--   Let $A$ be an $n \times n$ Hermitian matrix over an `RCLike` field $\mathbb{K}$, with spectral decomposition $A = U \operatorname{diag}(\lambda) U^{\mathsf H}$ ($U$ the eigenvector unitary, $\lambda_i$ the eigenvalues). For a real function $f : \mathbb{R} \to \mathbb{R}$, the project defines the spectral functional calculus
--   $$\operatorname{specMap}(A, f) \;=\; U \operatorname{diag}(f(\lambda_1), \dots, f(\lambda_n))\, U^{\mathsf H}.$$
--
--   **Statement.** For every vector $x \in \mathbb{K}^n$, writing $c = U^{\mathsf H} x$ for its eigenbasis coordinates,
--   $$\operatorname{Re}\bigl( x^{\mathsf H}\, \operatorname{specMap}(A,f)\, x \bigr) \;=\; \sum_{i} f(\lambda_i)\, \|c_i\|^2 .$$
--
--   That is, the Hermitian quadratic form of $f(A)$ diagonalizes in the eigenbasis of $A$ with weights $f(\lambda_i)$. In the module `Zeta23.LinAlg.HermitianPosPart` this identity drives the positivity statements about the Hermitian positive part $A_+ = \operatorname{specMap}(A, t \mapsto t^+)$: it is consumed by `RHLinalg.posDefOn_range_hermPosPart` (Sylvester, easy direction) and by `Zeta23.Tail.traceNorm_le_of_hasSum_vecMulVec` in the tail estimates of the matrix-variational argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/HermitianPosPart.lean#L75-L98

import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex

open Matrix Finset Unitary
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.hermForm_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (specMap hA f *ᵥ x))
      = ∑ i, f (hA.eigenvalues i) *
          ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by sorry
