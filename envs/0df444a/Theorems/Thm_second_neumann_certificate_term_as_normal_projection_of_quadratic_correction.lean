-- Prove2me | Theorems.Thm_second_neumann_certificate_term_as_normal_projection_of_quadratic_correction
-- name    : second_neumann_certificate_term_as_normal_projection_of_quadratic_correction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:58:18.442635+00:00
-- url     : https://prove2.me/theorems/11bcc492-f91e-419d-b1a1-06ad9f46b593
-- statement:
--   This is the algebraic identification of the second Neumann certificate term with the normal projection of the unprojected quadratic correction.
--
--   The proof of Lemma 4.6 expands the quadratic correction into five mutually exclusive index-coincidence classes:
--   $$
--   \omega_1=\omega_2=\omega_3,\quad
--   \omega_1\ne\omega_2=\omega_3,\quad
--   \omega_1=\omega_3\ne\omega_2,\quad
--   \omega_1=\omega_2\ne\omega_3,\quad
--   \omega_1,\omega_2,\omega_3\text{ pairwise distinct}.
--   $$
--   In the Lean interface these are, respectively,
--   `quadraticNeumannAllEqualContribution`,
--   `quadraticNeumannFirstIndexDistinctContribution`,
--   `quadraticNeumannMiddleIndexDistinctContribution`,
--   `quadraticNeumannLastIndexDistinctContribution`, and
--   `quadraticNeumannAllDistinctContribution`.
--   The theorem states that
--   $$
--   \operatorname{neumannCertificateTerm}_2
--   =
--   P_{T^\perp}(S_{111}+S_{123}+S_{132}+S_{112}+S_{\mathrm{distinct}}).
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 30, Section 6.3, equation (6.20).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem second_neumann_certificate_term_as_normal_projection_of_quadratic_correction
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    neumannCertificateTerm Omega S p 2 =
      normalProjection S
        ((((quadraticNeumannAllEqualContribution Omega S p +
          quadraticNeumannFirstIndexDistinctContribution Omega S p) +
          quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
          quadraticNeumannLastIndexDistinctContribution Omega S p) +
          quadraticNeumannAllDistinctContribution Omega S p) := by
  sorry
