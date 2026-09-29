-- Prove2me | Definitions.Def_Algebra_QubitTrade_Resolution
-- name    : Algebra_QubitTrade_Resolution
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:54:05.951089+00:00
-- url     : https://prove2.me/theorems/c449571c-1a7b-4a2d-aa00-8f112ac90403
-- title:
--   Aether Catalog definitions — Algebra_QubitTrade_Resolution
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QubitTrade.Resolution`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QubitTrade/Resolution.lean by skeleton subtraction
import Mathlib

/-!
# QUBIT-TRADE I: the resolution threshold of continued-fraction order recovery

Shor's order-finding algorithm returns a phase estimate `x ≈ k / r`, where
`r = ord_N(a)` and `0 ≤ k < r`, and the classical post-processing recovers `k/r`
(hence `r`) by continued fractions.  If the phase register is *truncated* to its
top `t` bits, the estimate is only known to accuracy `2^{-(t+1)}`.

The experiment QUBIT-TRADE measured a truncation threshold `t_min ≈ 2·log₂ r`.
This file proves that this threshold is **exact**, as a two-sided statement about
the *information* carried by a `t`-bit phase:

* `QubitTrade.rat_den_separation` — two distinct rationals are at distance at
  least `1/(den₁ · den₂)` (the Farey separation bound);
* `QubitTrade.cf_target_unique` — **sufficiency**: if `R^2 ≤ 2^t`, i.e.
  `t ≥ 2 log₂ R`, then at most one rational of denominator `≤ R` is compatible
  with a `t`-bit phase, so the continued-fraction target — and with it the order
  — is uniquely determined;
* `QubitTrade.order_unique_of_resolution` — the order-level corollary;
* `QubitTrade.cf_target_ambiguous` — **necessity**: if `2^t < R(R-1)`, i.e.
  `t < 2 log₂ R` up to one bit, there is a phase compatible with *two* distinct
  reduced fractions of denominator `≤ R`, realised by two distinct orders
  `R` and `R-1`.  No post-processing can separate them.
* `QubitTrade.threshold_two_sided` — the two statements packaged: the threshold
  sits in the window `R(R-1) ≤ 2^t < R^2`, i.e. `t_min = ⌈2 log₂ R⌉ ± 1`.
* `QubitTrade.linear_register_ambiguous` — the refutation of the predicted
  `log r + O(log log r)` register: for every constant `c`, a register of
  `log₂ R + c` bits is ambiguous as soon as `R > 2^c + 1`.

Everything is unconditional and model-free: it is a statement about how many
rationals of bounded denominator fit inside an interval of width `2^{-t}`.
-/

namespace QubitTrade

open scoped Rat

/-! ## Farey separation -/


/-! ## The truncated-register measurement model -/

/-- The resolution of a `t`-bit phase register: an outcome `m` pins the phase down
to the interval of radius `2^{-(t+1)}` around `m / 2^t`. -/
noncomputable def res (t : ℕ) : ℝ := ((2:ℝ) ^ (t + 1))⁻¹


/-- A rational `q` is *compatible* with the phase `x` read off a `t`-bit register
if it lies within the register's resolution of `x`. -/
def Compatible (t : ℕ) (x : ℝ) (q : ℚ) : Prop := |x - (q : ℝ)| < res t

/-- The order fraction `k / r` produced by an order-`r` Shor sample. -/
def orderFrac (k r : ℕ) : ℚ := (k : ℚ) / (r : ℚ)



/-! ## Sufficiency: `t ≥ 2 log₂ R` determines the continued-fraction target -/



/-! ## Necessity: below the quadratic threshold the target is ambiguous -/



/-! ## The two-sided threshold -/



end QubitTrade


