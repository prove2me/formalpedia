-- Prove2me | Definitions.Def_Zeta23_Tail_RankOne
-- name    : Zeta23_Tail_RankOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:11:16.286295+00:00
-- url     : https://prove2.me/theorems/56618ec6-38bd-4440-a8bd-48a44190b440
-- title:
--   Trace norm of a Hermitian matrix via eigenvalues
-- statement:
--   The linear-algebra device of [prop:tail] (the paper's §4.2): for a Hermitian matrix $E$ (witnessed by `hE : E.IsHermitian`), the trace norm is *defined* as the sum of the absolute values of its eigenvalues,
--   $$\lVert E\rVert_1 \;:=\; \sum_i |\lambda_i(E)|,$$
--   which for Hermitian $E$ coincides with the sum of singular values. This definition deliberately avoids Schatten-norm machinery.
--
--   Note the transpose convention: the tail matrix is a sum of terms $m_\rho\,u_\rho u_\rho^{\mathsf T}$ (`Matrix.vecMulVec`, transpose and **not** conjugate-transpose), since the vectors $u_\rho=(\hat\varphi(\gamma_\rho-\tau_k))_k$ are genuinely complex for off-line zeros and the paper's $E$ is complex-symmetric termwise; Hermitian-ness of the total (from the $\rho\mapsto1-\bar\rho$ symmetry) enters as the hypothesis `hE`.
--
--   **Role.** The surrounding module proves the paper's chain "$\lVert E\rVert\le\sum_{\gamma\notin I'}m_\rho\lVert u_\rho\rVert_2^2$ [eq:Enormsum], and the trace-norm bound follows from the same chain since $\lVert uu^{\mathsf T}\rVert_1=\lVert u\rVert_2^2$": both the operator-norm shape $\forall i,\ |\lambda_i(E)|\le\theta$ (as consumed by `RHLinalg.weyl_posIndexAbove_le`) and $\mathrm{traceNorm}\,\hat E\le\theta_0/(aL)$ follow from one inequality $\mathrm{traceNorm}\le\sum_\rho c_\rho\lVert u_\rho\rVert_2^2$, proved directly in the eigenbasis with Parseval. The trace norm is consumed in [prop:zeroside-rank] via $|\operatorname{tr}\hat E|\le\lVert\hat E\rVert_1$ and $\lVert\hat E\rVert_F\le\lVert\hat E\rVert_1$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/RankOne.lean, docstring tag [prop:tail]

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/RankOne.lean — the linear-algebra step of [prop:tail] (the paper §4.2):
eigenvalue bounds for a (possibly infinite) sum of rank-one matrices m_ρ u_ρ u_ρᵀ.


Paper, verbatim (proof of [prop:tail]): "Since E = ∑_{γ∉I'} m_ρ u_ρ u_ρᵀ and
‖uuᵀ‖ = ‖u‖₂², ‖E‖ ≤ ∑_{γ∉I'} m_ρ ‖u_ρ‖₂²  [eq:Enormsum]" … "The trace-norm bound follows
from the same chain, since ‖uuᵀ‖₁ = ‖u‖₂² as well".

Design (avoiding Schatten-norm machinery): the trace norm of a Hermitian
matrix is DEFINED here as traceNorm hE := ∑ᵢ |λᵢ(E)|, and the operator-norm bound is
delivered in the shape RHLinalg.weyl_posIndexAbove_le consumes, namely ∀ i, |λᵢ(E)| ≤ θ.
Both follow from one inequality, traceNorm hE ≤ ∑_ρ c_ρ ‖u_ρ‖₂², proved directly in the
eigenbasis: λᵢ = vᵢ* E vᵢ = ∑_ρ c_ρ ⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩, |⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩| ≤ (|⟨vᵢ,u_ρ⟩|² +
|⟨vᵢ,ū_ρ⟩|²)/2, and Parseval ∑ᵢ|⟨vᵢ,w⟩|² = ‖w‖² for the unitary eigenvector matrix.
NOTE u_ρ u_ρᵀ (Matrix.vecMulVec u u), NOT u_ρ u_ρ*: the u_ρ = (φ̂(γ_ρ − τ_k))_k are complex
for off-line zeros and the paper's E is complex-symmetric termwise; Hermitian-ness of the
total (from the ρ ↦ 1−ρ̄ symmetry) is taken as the hypothesis hE.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace norm ‖E‖₁ of a Hermitian matrix, DEFINED as ∑ᵢ |λᵢ(E)| (= sum of singular values
for Hermitian E). Paper: "the trace norm ‖Ê‖₁" in [prop:tail]; consumed in
[prop:zeroside-rank] via |tr Ê| ≤ ‖Ê‖₁ and ‖Ê‖_F ≤ ‖Ê‖₁ (both proved below). -/
def traceNorm {E : Matrix n n ℂ} (hE : E.IsHermitian) : ℝ := ∑ i, |hE.eigenvalues i|









end Tail
end Zeta23


