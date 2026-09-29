-- Prove2me | Theorems.Thm_FactoringBarriers_tendsto_rpow_mul_log_rpow_div_atTop
-- name    : FactoringBarriers.tendsto_rpow_mul_log_rpow_div_atTop
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:49:23.401693+00:00
-- url     : https://prove2.me/theorems/f451610d-da33-4471-b484-19598f4fad6b
-- title:
--   Key growth comparison: `x^α (log x)^{1-α} = o(x)` when `α < 1`.
-- statement:
--   Key growth comparison: `x^α (log x)^{1-α} = o(x)` when `α < 1`.
--
--   ```lean
--   theorem FactoringBarriers.tendsto_rpow_mul_log_rpow_div_atTop{α : ℝ} (hα1 : α < 1) :
--       Tendsto (fun x : ℝ => x ^ α * (Real.log x) ^ (1 - α) / x) atTop (𝓝 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/AsymptoticLadder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/AsymptoticLadder.lean#L116

-- Thm stub generated from Cryptography/FactoringBarriers/AsymptoticLadder.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder

/-!
# The Asymptotic Ladder for Classical Factoring Barriers

This file develops the *quantitative* backbone of the conditional-impossibility
framework for classical integer factoring.  Every known classical factoring
resource comes with a running-time barrier, and each barrier is expressed in
terms of the bit-size parameter `x = log N`.

The three shapes that occur are

* `x ↦ exp (b * x)` (exponential; e.g. `N^{1/4}` for Pollard rho, `b = 1/4`);
* `Lfun α c x = exp (c * x^α * (log x)^(1-α))` (subexponential `L_N[α, c]`;
  e.g. `L_N[1/3,c]` for the number field sieve, `L_p[1/2,√2]` for ECM);
* `x ↦ C * x^d` (polynomial — the target of a hypothetical fast algorithm).

Main results:

* `Superpoly_exp_rpow`  : `exp (c * x^α)` is superpolynomial for `c, α > 0`;
* `Lfun_superpoly`      : `L[α,c]` is superpolynomial for `0 < α ≤ 1`, `c > 0`;
* `Lfun_subexp`         : `L[α,c]` is *sub*exponential for `0 < α < 1`;
* `not_polyBounded_of_superpoly` : a superpolynomial lower bound rules out
  polynomially bounded running time.

Together these say that the `L`-functions occupy a genuine intermediate rung of
the ladder: strictly above every polynomial and strictly below every exponential.
-/

open FactoringBarriers

open Filter Real
open scoped Topology

/-! ## Growth classes -/





/-! ## Superpolynomiality is inherited by domination -/


/-! ## The basic exponential rung -/



/-! ## The `L`-functions are superpolynomial -/



/-! ## The `L`-functions are subexponential -/

theorem FactoringBarriers.tendsto_rpow_mul_log_rpow_div_atTop{α : ℝ} (hα1 : α < 1) :
    Tendsto (fun x : ℝ => x ^ α * (Real.log x) ^ (1 - α) / x) atTop (𝓝 0) := by sorry
