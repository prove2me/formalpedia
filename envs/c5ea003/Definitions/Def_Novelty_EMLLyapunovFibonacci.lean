-- Prove2me | Definitions.Def_Novelty_EMLLyapunovFibonacci
-- name    : Novelty_EMLLyapunovFibonacci
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:18:45.468961+00:00
-- url     : https://prove2.me/theorems/b4e21c2a-45dd-44ad-9aaf-0e79d48bd867
-- title:
--   Aether Catalog definitions — Novelty_EMLLyapunovFibonacci
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EMLLyapunovFibonacci`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EMLLyapunovFibonacci.lean by skeleton subtraction
import Mathlib

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

namespace EMLLyapunovFib

/-! ## 1.  Binet asymptotics -/



/-! ## 2.  The exact exponent -/



/-! ## 3.  The state trajectory of the two-tap unit -/

/-- The Fibonacci companion matrix: the one-step state map of the two-tap unit. -/
def fibCompanion : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

/-- The state of the two-tap unit after `n` steps, started from `(1, 0)`. -/
def fibState (n : ℕ) : Fin 2 → ℝ := ![Nat.fib (n + 1), Nat.fib n]






end EMLLyapunovFib


