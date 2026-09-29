-- Prove2me | Theorems.Thm_tangent_sampling_concentration_implies_sampled_tangent_operator_frobenius_bound_pos
-- name    : tangent_sampling_concentration_implies_sampled_tangent_operator_frobenius_bound_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-22T03:32:10.245034+00:00
-- url     : https://prove2.me/theorems/2c56e6bc-6ef6-477b-9d2d-098432175069
-- statement:
--   Corrected variant (adds the omitted 0<p and 0≤ε hypotheses, missing from the disproved c756305c). If the sampling rate p is positive, 0≤ε≤1/2, and the tangent sampling operator concentrates around its Bernoulli mean at scale ε (TangentSamplingConcentration), then for every tangent-space matrix X the sampled matrix satisfies the Frobenius bound ‖P_Ω X‖_F ≤ √(3p/2)·‖X‖_F. (Candès–Recht 2009, arXiv:0805.4471, §4.2.)
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471), Section 4.2

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_sampling_concentration_implies_sampled_tangent_operator_frobenius_bound_pos
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p epsilon : ℝ) :
    0 < p → 0 ≤ epsilon →
    epsilon ≤ (1 : ℝ) / 2 →
    TangentSamplingConcentration Omega S p epsilon →
    SampledTangentOperatorFrobeniusBound Omega S
      (Real.sqrt (((3 : ℝ) * p) / 2)) := by sorry
