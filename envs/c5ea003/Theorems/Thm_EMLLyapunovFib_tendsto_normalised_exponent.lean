-- Prove2me | Theorems.Thm_EMLLyapunovFib_tendsto_normalised_exponent
-- name    : EMLLyapunovFib.tendsto_normalised_exponent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:34:15.085124+00:00
-- url     : https://prove2.me/theorems/65326aea-9087-4933-a96d-a5ed4cd89a66
-- title:
--   Normalisation puts the two-tap unit exactly at the edge of chaos.
-- statement:
--   **Normalisation puts the two-tap unit exactly at the edge of chaos.**  Dividing the
--   recurrent weights by `φ` rescales the state by `φ^{-n}`, and the resulting exponent is
--   exactly `0` — neither exploding nor vanishing gradients.
--
--   ```lean
--   theorem EMLLyapunovFib.tendsto_normalised_exponent:
--       Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (‖fibState n‖ / φ ^ n)) Filter.atTop (𝓝 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EMLLyapunovFibonacci.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EMLLyapunovFibonacci.lean#L171

-- Thm stub generated from Novelty/EMLLyapunovFibonacci.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovFibonacci

/-!
# Lyapunov Exponents for Recurrent EML Architectures III: the two-tap linear unit

The simplest genuinely recurrent EML architecture with memory depth `2` is the *two-tap
linear recurrent unit*

`h_{t+1} = h_t + h_{t-1}`,

whose one-step state map is the Fibonacci companion matrix `M = !![1, 1; 1, 0]`.
This file computes its maximum Lyapunov exponent **exactly**:

`λ = log φ`,  where `φ = (1 + √5)/2` is the golden ratio,

and derives the two consequences that matter for training such an architecture:

* `log_goldenRatio_pos` — `λ > 0`, so the unnormalised two-tap unit *provably* suffers
  exploding gradients: the state norm grows like `φ^T`.
* `tendsto_normalised_exponent` — rescaling the recurrent weights by `φ⁻¹` puts the
  architecture exactly at the edge of chaos, exponent `0`.

The computation is a bridge between number theory (Binet's formula, the golden ratio) and
recurrent-network dynamics: the exact exponent is a quadratic irrational, and the
`φ`-eigenvector `(φ, 1)` of the companion matrix is the exact unstable direction.

## Main results

* `tendsto_fib_div_goldenRatio_pow` — `fib n / φ ^ n → 1/√5`.
* `tendsto_log_fib` — `(1/n) log (fib n) → log φ` (the exact exponent).
* `fibState_succ`, `norm_fibState` — the two-tap unit's state trajectory and its sup norm.
* `tendsto_fibState_exponent` — the exact maximum Lyapunov exponent of the two-tap unit.
* `fibCompanion_eigenvector` — `(φ, 1)` is the exact unstable eigendirection.
* `tendsto_normalised_exponent` — the `φ⁻¹`-normalised unit has exponent exactly `0`.
-/

open Filter Topology Real
open scoped goldenRatio

open EMLLyapunovFib

/-! ## 1.  Binet asymptotics -/



/-! ## 2.  The exact exponent -/



/-! ## 3.  The state trajectory of the two-tap unit -/

theorem EMLLyapunovFib.tendsto_normalised_exponent:
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log (‖fibState n‖ / φ ^ n)) Filter.atTop (𝓝 0) := by sorry
