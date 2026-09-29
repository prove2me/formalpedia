-- Prove2me | Theorems.Thm_RHLinalg_posDefOn_range_hermPosPart
-- name    : RHLinalg.posDefOn_range_hermPosPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:38:26.314279+00:00
-- url     : https://prove2.me/theorems/c9b8620f-d020-4ec3-a466-63a54e89b183
-- title:
--   Sylvester's inequality (easy direction): $A$ is positive definite on $\operatorname{range} A_+$
-- statement:
--   Let $A$ be an $n \times n$ Hermitian matrix over an `RCLike` field $\mathbb{K}$, with spectral decomposition $A = U \operatorname{diag}(\lambda) U^{\mathsf H}$, and let $A_+ = U \operatorname{diag}(\lambda^+) U^{\mathsf H}$ be its Hermitian positive part (`hermPosPart`, obtained by applying $t \mapsto \max(t,0)$ to the eigenvalues).
--
--   **Statement.** The Hermitian form of $A$ is positive definite on the range of $x \mapsto A_+ x$:
--   $$\forall\, z \in \operatorname{range}(A_+),\ z \ne 0 \;\Longrightarrow\; \operatorname{Re}(z^{\mathsf H} A z) > 0.$$
--
--   The proof: for $z = A_+ y$, the eigenbasis coordinates $c = U^{\mathsf H} z$ satisfy $c_i = \lambda_i^+ (U^{\mathsf H} y)_i$, so $c_i = 0$ whenever $\lambda_i \le 0$; hence $z^{\mathsf H} A z = \sum_{\lambda_i > 0} \lambda_i |c_i|^2 \ge 0$, and $z \ne 0$ forces a strictly positive term. Since $\operatorname{range}(A_+)$ has dimension equal to the positive index $n_+(A)$, this is the easy direction of the subspace characterization of $n_+$ in Sylvester's law of inertia (paper reference `lem:inertia`).
--
--   In the module `Zeta23.LinAlg.Sylvester` it is consumed by the subadditivity lemma `RHLinalg.posIndex_add_le` and by the zero-side block estimates `Zeta23.ZeroSide.ZeroBlockData.posIndex_blockA_le`, `posIndex_blockQ_le`, and `Zeta23.ZeroSide.posIndex_smul_pos` of the matrix-variational argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/Sylvester.lean#L115-L178, docstring tag [lem:inertia]

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester

open Matrix Finset Submodule
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
open Unitary

theorem RHLinalg.posDefOn_range_hermPosPart {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    PosDefOn A (LinearMap.range (hermPosPart hA).mulVecLin) := by sorry
