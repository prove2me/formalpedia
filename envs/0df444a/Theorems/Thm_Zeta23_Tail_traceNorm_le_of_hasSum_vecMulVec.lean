-- Prove2me | Theorems.Thm_Zeta23_Tail_traceNorm_le_of_hasSum_vecMulVec
-- name    : Zeta23.Tail.traceNorm_le_of_hasSum_vecMulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:46:17.240613+00:00
-- url     : https://prove2.me/theorems/d1162388-36fd-41a5-96fb-9f256a4bce26
-- title:
--   Trace-norm bound for a convergent sum of rank-one matrices $\sum c_\rho\, u_\rho u_\rho^{\mathsf T}$
-- statement:
--   **Setup.** Let $E$ be a Hermitian $n \times n$ complex matrix and `traceNorm hE` $:= \sum_i |\lambda_i(E)|$ the sum of the absolute values of its eigenvalues (equal to the sum of singular values for Hermitian $E$). Let $\iota$ be an arbitrary index type, $c : \iota \to \mathbb{R}$ nonnegative coefficients, and $u : \iota \to \mathbb{C}^n$ vectors. Here `vecMulVec (u ρ) (u ρ)` is the *unconjugated* outer product $u_\rho u_\rho^{\mathsf T}$ (entries $u_\rho(j)\,u_\rho(k)$, no complex conjugation) — this matches the zero-side matrices, whose symmetry is $\rho \mapsto 1 - \bar\rho$ rather than conjugate-transpose entry by entry.
--
--   **Statement.** Suppose (in the sense of Lean's `HasSum`, i.e. unconditional convergence of the nets of finite partial sums):
--   $$\sum_{\rho} c_\rho \sum_{k} \|u_\rho(k)\|^{2} = S \qquad\text{and}\qquad \sum_{\rho} c_\rho\, u_\rho u_\rho^{\mathsf T} = E.$$
--   Then
--   $$\|E\|_1 \;=\; \sum_i |\lambda_i(E)| \;\le\; S.$$
--   This is the trace-norm form of [eq:Enormsum], resting on the paper's observations "$\|u u^{\mathsf T}\| = \|u\|_2^2$" and "$\|u u^{\mathsf T}\|_1 = \|u\|_2^2$ as well".
--
--   **Role.** The linear-algebra engine of the tail bound in `Zeta23.Tail.RankOne`: applied to $E = \kappa\cdot(G - A)$ decomposed over tail zeros with $c_\rho = \kappa\,m_\rho$, it gives `TailHyp.traceNorm_smul_Ez_le` and hence the bounds $\|\tilde E\|_1 \le \theta_0$ and $\|\hat E\|_1 \le \theta_0/(aL)$ of Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail/RankOne.lean#L77-L164, docstring tag [eq:Enormsum]

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_Tail_RankOne

open Matrix Finset
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Zeta23.Tail.traceNorm_le_of_hasSum_vecMulVec {ι : Type*} {E : Matrix n n ℂ}
    (hE : E.IsHermitian) (c : ι → ℝ) (hc : ∀ ρ, 0 ≤ c ρ) (u : ι → n → ℂ) {S : ℝ}
    (hS : HasSum (fun ρ => c ρ * ∑ k, ‖u ρ k‖ ^ 2) S)
    (hEsum : HasSum (fun ρ => ((c ρ : ℝ) : ℂ) • vecMulVec (u ρ) (u ρ)) E) :
    traceNorm hE ≤ S := by sorry
