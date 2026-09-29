-- Prove2me | Theorems.Thm_RateDial_count_const_of_period_dvd
-- name    : RateDial.count_const_of_period_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:47.530025+00:00
-- url     : https://prove2.me/theorems/dd2f1f49-0a1a-42ea-b032-c8748266b9d5
-- title:
--   Flat composition, general form.
-- statement:
--   **Flat composition, general form.**  For an `m`-periodic classifier and a
--   window length that is a multiple of `m`, every window anywhere on the line has
--   exactly the same class populations.
--
--   ```lean
--   theorem RateDial.count_const_of_period_dvd{m : ℕ} {f : ℤ → α} (hper : PeriodicClass m f)
--       {L q : ℕ} (hL : L = m * q) (a : ℤ) (c : α) :
--       count f a L c = count f 0 L c := by sorry
--   /-! ## Quantitative version: window length not a multiple of the period -/
--
--
--
--
--   /-! ## Every residue-type carrier of `j` (and of `j² - N`) is periodic -/
--
--
--
--
--   /-! ## Capstone: no residue mixture removes any part of the excess -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/MixtureRateDialResidueCarriers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/MixtureRateDialResidueCarriers.lean#L106

-- Thm stub generated from Shared/MixtureRateDialResidueCarriers.lean
import Mathlib
import Definitions.Def_Shared_MixtureRateDialBaseline
import Definitions.Def_Shared_MixtureRateDialCells
import Definitions.Def_Shared_MixtureRateDialResidueCarriers

/-!
# No residue carrier is a position dial (Part III): the named follow-up, one family removed

Context: experiment 588c / paper 242 leaves the named follow-up *"identify the
non-divisibility carrier"*, with pre-named candidate family (i): `j`-arithmetic
beyond small-prime divisibility — higher-order residues of `v = j² - N`, bit
structure of `j`, quadratic-character / Legendre patterns mod `p > 7`.

This file removes **that entire family at once**, at every modulus and every
bit length.  The mechanism is the one isolated in Part I, but the divisibility
grid plays no special role in it:

> Every classifier of `j` that factors through `ZMod m` — divisibility patterns,
> Legendre symbols, higher power residues, low bit patterns, any Boolean
> combination of them — has *position independent* window composition as soon as
> the window length is a multiple of `m`.  By Part II its mixture family is a
> ray, so it removes exactly `0 %` of a positional excess.

Main results.

* `count_add`, `count_le` — basic window-count calculus.
* `count_const_of_period_dvd` — flat composition for any `m`-periodic classifier
  and window length a multiple of `m`.
* `count_drift_le_mod` — the *quantitative* version for a window length that is
  not a multiple: the composition of two windows can differ by at most
  `L % m < m` members, i.e. a relative drift `< m / L`.
* `periodicClass_of_zmod`, `residueCarrier_periodic`, `legendreCarrier_periodic`
  — every residue-type carrier of `v = j² - N` is periodic.
* `residue_mixture_excess_survives` — the capstone: the residual excess over any
  residue-class mixture equals the excess over the plain shape.
* `positional_carrier_is_aperiodic` — contrapositive and the actual content of
  the follow-up: **a carrier that moves the excess cannot factor through any
  `ZMod m` with `m ∣ L`; the non-divisibility carrier must be aperiodic in `j`.**
-/

open RateDial

open Finset

variable {α : Type*} [DecidableEq α]

/-! ## Periodic classifiers and window counts -/

theorem RateDial.count_const_of_period_dvd{m : ℕ} {f : ℤ → α} (hper : PeriodicClass m f)
    {L q : ℕ} (hL : L = m * q) (a : ℤ) (c : α) :
    count f a L c = count f 0 L c := by sorry
