-- Prove2me | Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
-- name    : Cryptography_FactoringBarriers_AsymptoticLadder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:02.956676+00:00
-- url     : https://prove2.me/theorems/28eb88d1-c395-4e2b-b251-2f9da544bd7d
-- title:
--   Aether Catalog definitions — Cryptography_FactoringBarriers_AsymptoticLadder
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FactoringBarriers.AsymptoticLadder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FactoringBarriers/AsymptoticLadder.lean by skeleton subtraction
import Mathlib

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

namespace FactoringBarriers

open Filter Real
open scoped Topology

/-! ## Growth classes -/

/-- `f` is *superpolynomial*: for every real exponent `d`, `f x / x ^ d → ∞`. -/
def Superpoly (f : ℝ → ℝ) : Prop :=
  ∀ d : ℝ, Tendsto (fun x => f x / x ^ d) atTop atTop

/-- `f` is *subexponential*: for every `ε > 0`, `f x / exp (ε * x) → 0`. -/
def Subexp (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun x => f x / Real.exp (ε * x)) atTop (𝓝 0)

/-- `f` is *polynomially bounded*: `f x ≤ C * x ^ d` for all large `x`. -/
def PolyBounded (f : ℝ → ℝ) : Prop :=
  ∃ C d : ℝ, ∀ᶠ x in atTop, f x ≤ C * x ^ d

/-- The subexponential complexity function `L_N[α, c] = exp (c (log N)^α (log log N)^{1-α})`,
written in the bit-size variable `x = log N`. -/
noncomputable def Lfun (α c x : ℝ) : ℝ :=
  Real.exp (c * x ^ α * (Real.log x) ^ (1 - α))

/-! ## Superpolynomiality is inherited by domination -/


/-! ## The basic exponential rung -/



/-! ## The `L`-functions are superpolynomial -/



/-! ## The `L`-functions are subexponential -/



/-! ## Superpolynomial lower bounds exclude polynomial time -/



/-! ## Separation of the rungs -/



end FactoringBarriers


