-- Prove2me | Theorems.Thm_ForkPinning_entropy_bool_eq_log_two_iff
-- name    : ForkPinning.entropy_bool_eq_log_two_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:34:09.487671+00:00
-- url     : https://prove2.me/theorems/5316c720-18f1-42cb-a4dc-7d437bb44e31
-- title:
--   Balanced forks, and only they, carry a full bit.
-- statement:
--   **Balanced forks, and only they, carry a full bit.**
--
--   ```lean
--   theorem ForkPinning.entropy_bool_eq_log_two_iff(Y : Ω → Bool) :
--       H Y = Real.log 2 ↔ prb Y true = 1 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningCapacity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningCapacity.lean#L89

-- Thm stub generated from Probability/ForkPinningCapacity.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
/-
# Capacity of a binary fork: one bit, attained exactly at the balanced coset forks

`ForkPinningCore` proves the two capacity bounds `I(X;Y) ≤ H Y` and `I(X;Y) ≤ log |κ|`.  For a
*binary* fork these combine into the hard ceiling `I ≤ log 2`: no congruence observable, however
large its conductor, can extract more than one bit from a two-valued splitting statistic.  This
file closes conjecture **C2** of `FUTURE_DIRECTIONS.md` by determining exactly when the ceiling
is attained.

Main results:

* `ForkPinning.entropy_bool_eq_log_two_iff` : `H Y = log 2` iff the fork is balanced (the strict
  maximum-entropy statement for two-valued statistics).
* `ForkPinning.mutualInfo_bool_le_log_two` : the one-bit ceiling.
* `ForkPinning.capacity_attained_iff` : `I(X;Y) = log 2` **iff** `X` determines `Y` *and* `Y` is
  balanced — capacity is attained exactly at the balanced forks that the observable pins.
* `ForkPinning.prb_hom_uniform` : a surjective character is uniformly distributed on a uniform
  group (the counting input).
* `ForkPinning.prb_signBool_true` : the sign of a uniformly random permutation of `Fin n`,
  `n ≥ 2`, is balanced.
* `ForkPinning.sign_attains_capacity` and `ForkPinning.sign_capacity_attained_iff` : for `Sₙ`
  the supremum `log 2` is attained, and *only* by the two forks `sign` and `¬sign` — the exact
  formal counterpart of the measurement "the only congruence structure in the whole `S₄`
  splitting is the sign".
-/


open ForkPinning

open Finset Real

/-! ## The strict maximum-entropy statement for binary forks -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem ForkPinning.entropy_bool_eq_log_two_iff(Y : Ω → Bool) :
    H Y = Real.log 2 ↔ prb Y true = 1 / 2 := by sorry
