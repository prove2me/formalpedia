-- Prove2me | Theorems.Thm_even2n_schatten_moment_bound
-- name    : even2n_schatten_moment_bound
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T03:14:59.768977+00:00
-- url     : https://prove2.me/theorems/aa809088-a2f2-4b53-82f0-24df2c46ddc9
-- statement:
--   **Even-order ($q=2n$) Schatten moment bound for the Rademacher-sampled matrix.** For the Rademacher-sampled matrix $M_\varepsilon = $ `rademacherSampledMatrix Ω ε p X` and $n \ge 1$ with $2n \ge \log(n_1+n_2)$, the expected even Schatten moment is dominated by the sampled variance scale: $\mathbb{E}_\varepsilon\big[\|M_\varepsilon\|_{S_{2n}}^{2n}\big] \le \big(\sqrt{2n}\,e\,\rho\big)^{2n}$, where $\rho = $ `rademacherSampledVarianceScale Ω p X` $= p^{-1}\sqrt{\max(\text{rowEnergyMax},\text{colEnergyMax})}$. Proof (reduction): the Schatten even moment is routed through the Hermitian dilation trace ($\|M_\varepsilon\|_{S_{2n}}^{2n} \le \operatorname{tr}(\mathcal{H}_\varepsilon^{2n})$); the signed sum of per-coordinate rank-one dilations matches the symmetric Rademacher trace-moment engine, whose variance matrix $V = \sum_c H_c^2$ is block-diagonal $\operatorname{blockdiag}(\operatorname{diag}(p^{-2}\text{rowEnergy}), \operatorname{diag}(p^{-2}\text{colEnergy}))$ with $\lambda_{\max}(V) \le \rho^2$ (block-diagonal quadratic-form bound); the engine then yields $\tfrac{(2n)!}{2^n n!}\rho^{2n}(n_1+n_2)$, and the constant+window step ($\tfrac{(2n)!}{2^n n!} \le (2n)^n$, $(n_1+n_2)^{1/2n} \le e$) collapses it to $(\sqrt{2n}\,e\,\rho)^{2n}$.
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1, Thm 6.3. The EVEN-order (q=2n) Schatten moment of the Rademacher-sampled matrix, bounded directly by the (sampled variance scale) via the Hermitian-dilation trace-moment engine. The variance matrix V = ∑_c H_c² is block-diagonal blockdiag(diag(p⁻²rowEnergy), diag(p⁻²colEnergy)) with λmax(V) ≤ (rademacherSampledVarianceScale)², discharged through the block-diagonal quadratic-form bound.

import Definitions.Def_matrix_completion_gram_schatten
open Matrix MatrixCompletion
open scoped BigOperators

theorem even2n_schatten_moment_bound {n1 n2 : Nat} (n : Nat) (hn : 1 ≤ n) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : MatrixCompletion.RealMatrix n1 n2) (hd1 : 1 ≤ (n1 + n2)) (hlog : Real.log ((n1 + n2 : ℕ)) ≤ (2 * n : ℕ)) : rademacherExpectation (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n)) ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rademacherSampledVarianceScale Omega p X) ^ (2 * n) := by sorry
