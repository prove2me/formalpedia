-- Prove2me | solution 3 for positive_bernoulli_least_squares_certificate_existence_from_tangent_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T05:42:25.769852+00:00
-- url     : https://prove2.me/submissions/eccbf21b-c575-4ea1-a08e-097367ae8802

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_tangent_sampling_concentration_implies_tangent_sampling_surjective_on_tangent
import Theorems.Thm_tangent_sampling_surjectivity_gives_supported_tangent_certificate
import Theorems.Thm_supported_tangent_certificate_set_has_frobenius_minimizer
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sign_matrix_mem_tangent_space

open MatrixCompletion
open scoped Classical BigOperators

/-!
Reduction: lift the deterministic chain
`tangent concentration ⇒ surjectivity ⇒ feasible point ⇒ least-squares
certificate` to a Bernoulli event-probability lower bound.

Source: Candès–Recht 2009 (arXiv:0805.4471 v3) / CACM 55(6) 2012, §4.2,
"Construction of the dual certificate".  On the high-probability event that the
sampled tangent operator is `1/2`-concentrated (eq. (4.10)/(4.11)), `P_T P_Ω P_T`
is invertible on `T`, hence the tangent sampling operator is onto `T`
(`...concentration_implies_..._surjective_on_tangent`); surjectivity at the
in-tangent sign matrix (`sign_matrix_mem_tangent_space`) produces a feasible
`Ω`-supported matrix with `P_T Y = sign(M)`
(`..._surjectivity_gives_supported_tangent_certificate`); and the feasible set,
being nonempty and closed, admits the minimal-Frobenius least-squares certificate
(`supported_tangent_certificate_set_has_frobenius_minimizer`).  The event of
`1/2`-concentration is therefore contained in the event that a least-squares dual
certificate exists, so Bernoulli event-probability monotonicity
(`bernoulli_event_probability_mono`) transports the lower bound.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
          LeastSquaresDualCertificate Omega S Y) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hp hp1 hconc
  -- pointwise: `1/2`-concentration ⇒ a least-squares certificate exists
  have hincl : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
      (∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ, LeastSquaresDualCertificate Omega S Y) := by
    intro Omega hC
    -- concentration ⇒ surjectivity on T
    have hsurj : TangentSamplingOperatorSurjectiveOnT Omega S :=
      tangent_sampling_concentration_implies_tangent_sampling_surjective_on_tangent
        Omega S p hp hC
    -- surjectivity + sign matrix ∈ T ⇒ feasible supported matrix exists
    have hfeas : ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        VanishesOutside Omega Y ∧ tangentProjection S Y = signMatrix S :=
      tangent_sampling_surjectivity_gives_supported_tangent_certificate S Omega
        hsurj (sign_matrix_mem_tangent_space S)
    -- nonempty closed feasible set ⇒ minimal-Frobenius certificate
    exact supported_tangent_certificate_set_has_frobenius_minimizer S Omega hfeas
  -- event-probability monotonicity transports the lower bound
  have hmono :
      bernoulliEventProb p
          (fun Omega => TangentSamplingConcentration Omega S p ((1 : ℝ) / 2)) ≤
      bernoulliEventProb p
          (fun Omega => ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
            LeastSquaresDualCertificate Omega S Y) :=
    bernoulli_event_probability_mono p _ _ (le_of_lt hp) hp1 hincl
  exact le_trans hconc hmono
