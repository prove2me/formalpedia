-- Prove2me | solution 1 for first_neumann_certificate_term_spectral_norm_le_diagonal_off_diagonal_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T05:14:10.601112+00:00
-- url     : https://prove2.me/submissions/51142c8f-836e-4878-b2ac-4ee85fbe06d7

import Theorems.Thm_first_neumann_certificate_term_as_negative_normal_projection_of_linear_correction
import Theorems.Thm_normal_projection_spectral_norm_le_original

open MatrixCompletion

/-!
Source: Candes-Recht 2008, Section 6.2, PDF p. 26, equation (6.8).  The proof
of Lemma 4.5 first bounds
`p^{-1} ||P_{T^\perp} P_Ω P_T H(E)||` by the unprojected centered correction
`p^{-1} ||(P_Ω-pI)H(E)||`, using `||P_{T^\perp}(X)|| <= ||X||`; equation
(6.8) then decomposes that correction into its diagonal and off-diagonal
parts `S_0 + S_1`.

Reduction: identify the Lean first certificate term as the negative normal
projection of the unprojected linear correction `S_0+S_1`; the sign is
irrelevant for the spectral norm, so the normal-projection contraction
`||P_{T^\perp}(X)|| <= ||X||` proves the comparison.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    spectralNorm (neumannCertificateTerm Omega S p 1) ≤
      spectralNorm
        (linearNeumannDiagonalContribution Omega S p +
          linearNeumannOffDiagonalContribution Omega S p) := by
  rw [first_neumann_certificate_term_as_negative_normal_projection_of_linear_correction]
  simpa [spectralNorm] using normal_projection_spectral_norm_le_original S
    (linearNeumannDiagonalContribution Omega S p +
      linearNeumannOffDiagonalContribution Omega S p)
