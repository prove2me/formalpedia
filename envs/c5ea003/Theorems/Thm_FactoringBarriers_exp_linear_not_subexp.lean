-- Prove2me | Theorems.Thm_FactoringBarriers_exp_linear_not_subexp
-- name    : FactoringBarriers.exp_linear_not_subexp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:09.974197+00:00
-- url     : https://prove2.me/theorems/2cf9a24e-5710-4a6e-b954-8dd3c2170813
-- title:
--   Genuine exponentials are *not* subexponential: `exp (b x)` with `b > 0`
-- statement:
--   Genuine exponentials are *not* subexponential: `exp (b x)` with `b > 0`
--   fails the subexponentiality test at `ε = b / 2`.
--
--   ```lean
--   theorem FactoringBarriers.exp_linear_not_subexp{b : ℝ} (hb : 0 < b) :
--       ¬ Subexp (fun x => Real.exp (b * x)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/AsymptoticLadder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/AsymptoticLadder.lean#L203

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



/-! ## Superpolynomial lower bounds exclude polynomial time -/



/-! ## Separation of the rungs -/

theorem FactoringBarriers.exp_linear_not_subexp{b : ℝ} (hb : 0 < b) :
    ¬ Subexp (fun x => Real.exp (b * x)) := by sorry
