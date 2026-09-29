-- Prove2me | Definitions.Def_Shared_MixtureRateDialResidueCarriers
-- name    : Shared_MixtureRateDialResidueCarriers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:04:04.812198+00:00
-- url     : https://prove2.me/theorems/8dd25b5d-5612-4cbd-9f42-a869e82387aa
-- title:
--   Aether Catalog definitions — Shared_MixtureRateDialResidueCarriers
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.MixtureRateDialResidueCarriers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/MixtureRateDialResidueCarriers.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_MixtureRateDialBaseline
import Definitions.Def_Shared_MixtureRateDialCells

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

namespace RateDial

open Finset

variable {α : Type*} [DecidableEq α]

/-! ## Periodic classifiers and window counts -/

/-- `f` classifies integers `m`-periodically. -/
def PeriodicClass (m : ℕ) (f : ℤ → α) : Prop := ∀ j : ℤ, f (j + m) = f j

/-- The number of `j` in the window `{a, …, a + L - 1}` with class `c`. -/
def count (f : ℤ → α) (a : ℤ) (L : ℕ) (c : α) : ℕ :=
  ∑ i ∈ Finset.range L, if f (a + i) = c then 1 else 0






/-! ## Quantitative version: window length not a multiple of the period -/




/-! ## Every residue-type carrier of `j` (and of `j² - N`) is periodic -/




/-! ## Capstone: no residue mixture removes any part of the excess -/

/-- Cell-resolved reference sums built from a general classifier `f` and a window
of length `L`. -/
noncomputable def classRefSum (f : ℤ → α) (L : ℕ) (B : ℝ → ℝ) (c : α) (t : ℝ) : ℝ :=
  (count f ⌊t⌋ L c : ℝ) * B t





end RateDial


