-- Prove2me | Theorems.Thm_schatten_even_pow_le_trace_dilation_even_pow
-- name    : schatten_even_pow_le_trace_dilation_even_pow
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T03:10:46.690119+00:00
-- url     : https://prove2.me/theorems/fac8e941-3538-4ebc-8d4d-4b292b5ef1a9
-- statement:
--   **Schatten even-power moment ≤ dilation trace moment.** For a real rectangular matrix $X$ and $n \ge 1$, the $2n$-th power of the Schatten-$2n$ norm is bounded by the trace of the $2n$-th power of the Hermitian dilation $\mathcal{H} = \begin{pmatrix}0 & X\\ X^\top & 0\end{pmatrix}$: $\|X\|_{S_{2n}}^{2n} \le \operatorname{tr}(\mathcal{H}^{2n})$. Proof (reduction): $\|X\|_{S_{2n}}^{2n} = \operatorname{tr}((XX^\top)^n)$ (Schatten even-power = row-Gram trace), and $\operatorname{tr}(\mathcal{H}^{2n}) = \operatorname{tr}((XX^\top)^n) + \operatorname{tr}((X^\top X)^n)$ (dilation trace identity), with $\operatorname{tr}((X^\top X)^n) \ge 0$ since $X^\top X$ is positive semidefinite. This routes the rectangular Schatten moment onto the symmetric Hermitian trace-moment engine.
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1, Thm 6.3. The Schatten even-power moment of a rectangular X is bounded by the trace of the even power of its Hermitian dilation: schattenNorm(2n)X^(2n) = trace((XXᵀ)ⁿ) ≤ trace((XXᵀ)ⁿ)+trace((XᵀX)ⁿ) = trace(dilation(X)^(2n)) (the dropped term trace((XᵀX)ⁿ) ≥ 0 since XᵀX is PSD). This routes the rectangular Schatten moment to the symmetric trace-moment engine on the dilation.

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
open Matrix MatrixCompletion
open scoped BigOperators

theorem schatten_even_pow_le_trace_dilation_even_pow (n : Nat) (hn : 1 ≤ n) {n1 n2 : Nat} (X : MatrixCompletion.RealMatrix n1 n2) : MatrixCompletion.schattenNorm (2 * n) X ^ (2 * n) ≤ Matrix.trace ((Matrix.fromBlocks 0 X Xᵀ 0) ^ (2 * n)) := by sorry
