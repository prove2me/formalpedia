-- Prove2me | Theorems.Thm_RHLinalg_vonNeumann_trace_ineq
-- name    : RHLinalg.vonNeumann_trace_ineq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:39:13.308793+00:00
-- url     : https://prove2.me/theorems/ea4f7dc1-dd3f-46b1-9775-808a1d00e193
-- title:
--   Von Neumann's trace inequality for Hermitian matrices: $\operatorname{Re}\operatorname{tr}(AB) \le \sum_i a_i b_i$
-- statement:
--   Let $A, B$ be $n \times n$ Hermitian matrices over an `RCLike` field. Write $a_1 \ge a_2 \ge \dots$ and $b_1 \ge b_2 \ge \dots$ for their eigenvalues sorted in decreasing order — in Lean these are Mathlib's `eigenvalues₀`, indexed by `Fin (Fintype.card n)` and antitone in the index.
--
--   **Statement.**
--   $$\operatorname{Re} \operatorname{tr}(A B) \;\le\; \sum_{i} a_i\, b_i ,$$
--   i.e. the trace pairing of two Hermitian matrices is maximized by pairing eigenvalues in matching order.
--
--   This is the Hermitian case of von Neumann's trace inequality. The formalized proof combines the eigenbasis identity `RHLinalg.re_trace_mul_eq_eigenvalue_bilinear` ($\operatorname{Re}\operatorname{tr}(AB)$ as an eigenvalue bilinear form weighted by $\|W_{kl}\|^2$ for a unitary $W$), the fact that this weight matrix is doubly stochastic (`RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary`), and the Birkhoff–rearrangement bound `RHLinalg.bilinear_doublyStochastic_le_of_monovary`.
--
--   In the module `Zeta23.LinAlg.VonNeumann` it is consumed by the rank–trace inequality `RHLinalg.rank_trace_ineq`, the key matrix-variational estimate feeding the assembly of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/VonNeumann.lean#L169-L202

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem RHLinalg.vonNeumann_trace_ineq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace
      ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by sorry
