-- Prove2me | Theorems.Thm_EulerMascheroniInformationBridge_exponentialKL_eq_zero_iff
-- name    : EulerMascheroniInformationBridge.exponentialKL_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:33:12.709983+00:00
-- url     : https://prove2.me/theorems/16ec597e-0bd8-4beb-ad9b-d199314f38c8
-- title:
--   Equality case of Gibbs' inequality for positive exponential rates.
-- statement:
--   Equality case of Gibbs' inequality for positive exponential rates.
--
--   ```lean
--   theorem EulerMascheroniInformationBridge.exponentialKL_eq_zero_iff{rate₁ rate₂ : ℝ}
--       (h₁ : 0 < rate₁) (h₂ : 0 < rate₂) :
--       exponentialKL rate₁ rate₂ = 0 ↔ rate₁ = rate₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/EulerMascheroniInformationBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/EulerMascheroniInformationBridge.lean#L221

-- Thm stub generated from Shared/EulerMascheroniInformationBridge.lean
import Mathlib
import Definitions.Def_Shared_EulerMascheroniInformationBridge

/-!
# Euler–Mascheroni constant as accumulated information divergence

This file connects analytic number theory with information theory.  For positive
rates `λ` and `μ`, the Kullback–Leibler divergence from an exponential law of rate
`λ` to one of rate `μ` has the closed form

`log (λ / μ) + μ / λ - 1`.

At the consecutive integer rates `λ = k+1`, `μ = k+2`, this is exactly the
`k`-th nonnegative summand in the classical series for the Euler–Mascheroni
constant.  Consequently, `γ` is the accumulated KL divergence along the chain
of exponential distributions with rates `1, 2, 3, ...`.
-/

open Real Filter Finset Topology

open EulerMascheroniInformationBridge

theorem EulerMascheroniInformationBridge.exponentialKL_eq_zero_iff{rate₁ rate₂ : ℝ}
    (h₁ : 0 < rate₁) (h₂ : 0 < rate₂) :
    exponentialKL rate₁ rate₂ = 0 ↔ rate₁ = rate₂ := by sorry
