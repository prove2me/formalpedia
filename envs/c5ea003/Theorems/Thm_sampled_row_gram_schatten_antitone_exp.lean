-- Prove2me | Theorems.Thm_sampled_row_gram_schatten_antitone_exp
-- name    : sampled_row_gram_schatten_antitone_exp
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-23T21:39:57.625602+00:00
-- url     : https://prove2.me/theorems/6dee255d-294f-4e46-b462-f67ab1f7b41c
-- statement:
--   **ℓ_q-Gram-vector antitone (row).** For a sampling probability `0 ≤ p`, real exponents `1 ≤ q ≤ q'`, and any real matrix `X`, the per-row sampled Gram-Schatten ℓ_q quantity decreases in the exponent: `sampledRowGramSchatten Ω p X q' ≤ sampledRowGramSchatten Ω p X q`. Here `sampledRowGramSchatten Ω p X q = (∑_i (p⁻¹ √(∑_{(i,j)∈Ω} X_{ij}²))^q)^{1/q}` is the ℓ_q norm of the per-row vector `p⁻¹ √(rowEnergy_i)`. This is the power-mean / ℓ_p-monotonicity inequality (Hardy–Littlewood–Pólya, *Inequalities* §2.10) applied to that nonnegative vector — the Gram-side analogue of the Schatten antitone `schatten_norm_antitone_exp`. It is the (d) analytic step of the Candès–Recht 2009 §6.1 matrix-Khintchine general-q reduction: the RHS Gram term `rowGS(2n)` for the even integer `2n ∈ [q, q+2)` is dominated by `rowGS(q)`. **Proof:** normalize by `A = (∑σ^q)^{1/q}`; the normalized entries `t_i = σ_i/A ≤ 1` give `t_i^{q'} ≤ t_i^q`, hence `∑ t_i^{q'} ≤ 1`, which rearranges to the claim (`A = 0` handled separately). The vector `σ_i = p⁻¹ √(rowEnergy_i)` is nonnegative since `0 ≤ p`.
-- source:
--   Hardy, Littlewood, Polya, Inequalities, 2nd ed. (Cambridge Univ. Press, 1952), Sec. 2.10 (power means / nesting of the l_p means); equivalently Horn & Johnson, Matrix Analysis. Used by the Candes-Recht 2009 (arXiv:0805.4471) Sec. 6.1 matrix-Khintchine general-q reduction: the RHS Gram-Schatten terms are decreasing in the exponent (the l_q-Gram-vector antitone step).

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion

theorem sampled_row_gram_schatten_antitone_exp {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 ≤ p) (X : MatrixCompletion.RealMatrix n1 n2) (q q' : Real) (hq : 1 ≤ q) (hqq' : q ≤ q') : MatrixCompletion.sampledRowGramSchatten Omega p X q' ≤ MatrixCompletion.sampledRowGramSchatten Omega p X q := by sorry
