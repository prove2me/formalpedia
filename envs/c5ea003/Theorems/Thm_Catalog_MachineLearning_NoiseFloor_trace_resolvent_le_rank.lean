-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_trace_resolvent_le_rank
-- name    : Catalog.MachineLearning.NoiseFloor.trace_resolvent_le_rank
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:28:25.536238+00:00
-- url     : https://prove2.me/theorems/0fecc243-a0a0-4b7f-ba58-10928775b8c7
-- title:
--   Frontier bound 3 (rank).
-- statement:
--   **Frontier bound 3 (rank).**  The effective dimension never exceeds the true
--   rank: null directions of the covariance are invisible to the noise floor.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.trace_resolvent_le_rank(hA : A.IsHermitian) (hpsd : A.PosSemidef) (hb : 0 < b) :
--       (A * (A + b • (1 : Matrix n n ℝ))⁻¹).trace ≤ (A.rank : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/TraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/TraceLemma.lean#L132

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








variable {A : Matrix n n ℝ} {b : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.trace_resolvent_le_rank(hA : A.IsHermitian) (hpsd : A.PosSemidef) (hb : 0 < b) :
    (A * (A + b • (1 : Matrix n n ℝ))⁻¹).trace ≤ (A.rank : ℝ) := by sorry
