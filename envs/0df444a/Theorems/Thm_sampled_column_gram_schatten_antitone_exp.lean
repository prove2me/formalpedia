-- Prove2me | Theorems.Thm_sampled_column_gram_schatten_antitone_exp
-- name    : sampled_column_gram_schatten_antitone_exp
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-23T21:40:27.145007+00:00
-- url     : https://prove2.me/theorems/1cefc36c-2dd1-4856-8799-414e20f60049
-- statement:
--   **ℓ_q-Gram-vector antitone (column).** For a sampling probability `0 ≤ p`, real exponents `1 ≤ q ≤ q'`, and any real matrix `X`, the per-column sampled Gram-Schatten ℓ_q quantity decreases in the exponent: `sampledColumnGramSchatten Ω p X q' ≤ sampledColumnGramSchatten Ω p X q`. Here `sampledColumnGramSchatten Ω p X q = (∑_j (p⁻¹ √(∑_{(i,j)∈Ω} X_{ij}²))^q)^{1/q}` is the ℓ_q norm of the per-column vector `p⁻¹ √(colEnergy_j)`. This is the power-mean / ℓ_p-monotonicity inequality (Hardy–Littlewood–Pólya, *Inequalities* §2.10) applied to that nonnegative vector — the Gram-side analogue of the Schatten antitone `schatten_norm_antitone_exp`. It is the (d) analytic step of the Candès–Recht 2009 §6.1 matrix-Khintchine general-q reduction: the RHS Gram term `colGS(2n)` for the even integer `2n ∈ [q, q+2)` is dominated by `colGS(q)`. **Proof:** normalize by `A = (∑σ^q)^{1/q}`; the normalized entries `t_j = σ_j/A ≤ 1` give `t_j^{q'} ≤ t_j^q`, hence `∑ t_j^{q'} ≤ 1`, which rearranges to the claim (`A = 0` handled separately). The vector `σ_j = p⁻¹ √(colEnergy_j)` is nonnegative since `0 ≤ p`.
-- source:
--   Hardy, Littlewood, Polya, Inequalities, 2nd ed. (Cambridge Univ. Press, 1952), Sec. 2.10 (power means / nesting of the l_p means); equivalently Horn & Johnson, Matrix Analysis. Used by the Candes-Recht 2009 (arXiv:0805.4471) Sec. 6.1 matrix-Khintchine general-q reduction: the RHS Gram-Schatten terms are decreasing in the exponent (the l_q-Gram-vector antitone step).

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion

theorem sampled_column_gram_schatten_antitone_exp {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 ≤ p) (X : MatrixCompletion.RealMatrix n1 n2) (q q' : Real) (hq : 1 ≤ q) (hqq' : q ≤ q') : MatrixCompletion.sampledColumnGramSchatten Omega p X q' ≤ MatrixCompletion.sampledColumnGramSchatten Omega p X q := by sorry
