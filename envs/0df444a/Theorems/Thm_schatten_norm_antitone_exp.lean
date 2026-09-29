-- Prove2me | Theorems.Thm_schatten_norm_antitone_exp
-- name    : schatten_norm_antitone_exp
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-23T18:34:50.171739+00:00
-- url     : https://prove2.me/theorems/f6a12b35-cd9a-4566-856f-46300e23d27b
-- statement:
--   **Schatten norms are antitone in the exponent.** For real exponents `1 ≤ q ≤ q'` and any real matrix `X`, the Schatten `q'`-norm is bounded by the Schatten `q`-norm: `schattenNorm q' X ≤ schattenNorm q X`. Equivalently, the ℓ_p-(quasi)norm of the singular-value vector decreases in `p`: `(∑_k σ_k(X)^{q'})^{1/q'} ≤ (∑_k σ_k(X)^q)^{1/q}`. This is the power-mean / ℓ_p-monotonicity inequality (Hardy–Littlewood–Pólya, *Inequalities* §2.10) applied to the singular values. It is the antitonicity invoked by the matrix-Khintchine even-q reduction `K-to-general-q` (CR2009 §6.1): since Schatten norms decrease in `q`, an even integer `2n ∈ [q, q+2)` dominates the Schatten-`q` moment, so the Buchholz even-integer bound drives the general-`q` case. **Proof:** normalize by `A = (∑σ^q)^{1/q}`; the normalized entries `t_k = σ_k/A` satisfy `∑ t_k^q = 1`, so each `t_k ≤ 1`, hence `t_k^{q'} ≤ t_k^q`, hence `∑ t_k^{q'} ≤ 1`, which rearranges to the claim (with the `A = 0` case handled separately).
-- source:
--   Hardy, Littlewood, Polya, Inequalities, 2nd ed. (Cambridge Univ. Press, 1952), Sec. 2.10 (power means / nesting of the l_p means); equivalently Horn & Johnson, Matrix Analysis (Schatten p-norms decrease in p). Used by the Candes-Recht 2009 (arXiv:0805.4471) Sec. 6.1 matrix-Khintchine even-q reduction.

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem schatten_norm_antitone_exp (n1 n2 : Nat) (q q' : Real) (hq : 1 ≤ q) (hqq' : q ≤ q') (X : MatrixCompletion.RealMatrix n1 n2) : MatrixCompletion.schattenNorm q' X ≤ MatrixCompletion.schattenNorm q X := by sorry
