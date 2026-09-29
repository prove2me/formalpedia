-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_resolvent_eq
-- name    : Catalog.MachineLearning.NoiseFloor.resolvent_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:29:09.004394+00:00
-- url     : https://prove2.me/theorems/59892ea9-fd31-4600-8f92-6e79f407ed6b
-- title:
--   Explicit resolvent.
-- statement:
--   **Explicit resolvent.**  For a positive semidefinite `A` and `b > 0`,
--   `(A + b•1)⁻¹` is the conjugate of the diagonal matrix `1/(μ i + b)`.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.resolvent_eq(hA : A.IsHermitian) (hpsd : A.PosSemidef) (hb : 0 < b) :
--       (A + b • (1 : Matrix n n ℝ))⁻¹ =
--         (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => (hA.eigenvalues i + b)⁻¹) *
--           star (hA.eigenvectorUnitary : Matrix n n ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/TraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/TraceLemma.lean#L72

-- Thm stub generated from MachineLearning/NoiseFloor/TraceLemma.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part III: the trace-lemma frontier

Round-6 hypothesis closure, Phase A.

Parts I and II worked with an abstract spectrum `a : ι → ℝ`.  This file closes
the loop with genuine matrices: for a real positive semidefinite covariance
`A` and noise level `b > 0` we build the resolvent `(A + b•1)⁻¹` explicitly out
of the spectral decomposition and prove the **trace lemma**

  `tr (A (A + b•1)⁻¹) = ∑ i, μ i / (μ i + b) = effDim μ b`,

where `μ` are the eigenvalues of `A`.  Consequently the exact minimum of the
spectral learning risk of Part II is the *analytic* quantity
`b · tr (A (A + b•1)⁻¹)` — the noise floor is a trace functional of the data
covariance alone.  We then push the frontier: the trace functional is squeezed
between `0` and `min (tr A / b) (rank A) (n)`.

## Main results

* `resolvent_eq`              — explicit diagonalisation of `(A + b•1)⁻¹`
* `trace_resolvent_eq_effDim` — the trace lemma
* `noiseFloor_eq_b_mul_trace` — the noise floor is `b · tr (A (A+b•1)⁻¹)`
* `isLeast_filterRisk_matrix` — variational form: the minimum risk of *every*
  spectral filter equals `b · tr (A (A+b•1)⁻¹)`
* `trace_resolvent_le_trace_div`, `trace_resolvent_le_card`,
  `trace_resolvent_le_rank` — the three frontier bounds
* `noiseFloor_matrix_le_min`  — `b·tr(A(A+b)⁻¹) ≤ min (tr A) (n b)`
-/

open Catalog.MachineLearning.NoiseFloor

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]


variable {A : Matrix n n ℝ} {b : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.resolvent_eq(hA : A.IsHermitian) (hpsd : A.PosSemidef) (hb : 0 < b) :
    (A + b • (1 : Matrix n n ℝ))⁻¹ =
      (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => (hA.eigenvalues i + b)⁻¹) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) := by sorry
