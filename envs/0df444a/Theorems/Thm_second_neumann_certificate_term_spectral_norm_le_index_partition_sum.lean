-- Prove2me | Theorems.Thm_second_neumann_certificate_term_spectral_norm_le_index_partition_sum
-- name    : second_neumann_certificate_term_spectral_norm_le_index_partition_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T16:52:49.722105+00:00
-- url     : https://prove2.me/theorems/aea984e5-a35f-443a-85b2-ee5bdac78297
-- statement:
--   This is the source-correct comparison for the second-order Neumann certificate term.
--
--   Let
--   $$
--   S_{111}+S_{123}+S_{132}+S_{112}+S_{\mathrm{distinct}}
--   $$
--   be the five-part expansion of the unprojected quadratic correction in Candes-Recht equation (6.20), grouped according to which of $\omega_1,\omega_2,\omega_3$ are equal. The second normal-projected certificate term is the normal projection of this correction, hence
--   $$
--   \|\operatorname{neumannCertificateTerm}_2\|
--   =
--   \|P_{T^\perp}(S_{111}+S_{123}+S_{132}+S_{112}+S_{\mathrm{distinct}})\|
--   \le
--   \|S_{111}+S_{123}+S_{132}+S_{112}+S_{\mathrm{distinct}}\|.
--   $$
--   Source: Candes-Recht 2008, PDF p. 30, Section 6.3, equation (6.20), together with the normal-projection contraction used before equation (6.5) on PDF p. 24.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem second_neumann_certificate_term_spectral_norm_le_index_partition_sum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    spectralNorm (neumannCertificateTerm Omega S p 2) ≤
      spectralNorm
        ((((quadraticNeumannAllEqualContribution Omega S p +
          quadraticNeumannFirstIndexDistinctContribution Omega S p) +
          quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
          quadraticNeumannLastIndexDistinctContribution Omega S p) +
          quadraticNeumannAllDistinctContribution Omega S p) := by
  sorry
