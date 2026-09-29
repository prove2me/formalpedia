-- Prove2me | solution 1 for RateDial.count_const_of_period_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:39:37.172147+00:00
-- url     : https://prove2.me/submissions/539937b3-c5cd-4eca-842b-6254f291a6c6

-- Sol generated from Shared/MixtureRateDialResidueCarriers.lean
import Mathlib
import Definitions.Def_Shared_MixtureRateDialBaseline
import Definitions.Def_Shared_MixtureRateDialCells
import Definitions.Def_Shared_MixtureRateDialResidueCarriers
import Theorems.Thm_RateDial_count_succ_of_period

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








/-! ## Quantitative version: window length not a multiple of the period -/




/-! ## Every residue-type carrier of `j` (and of `j² - N`) is periodic -/




/-! ## Capstone: no residue mixture removes any part of the excess -/







open RateDial in
theorem solution{m : ℕ} {f : ℤ → α} (hper : PeriodicClass m f)
    {L q : ℕ} (hL : L = m * q) (a : ℤ) (c : α) :
    count f a L c = count f 0 L c := by
  refine Int.induction_on a rfl (fun n ih => ?_) (fun n ih => ?_)
  · rw [count_succ_of_period hper _ hL]; exact ih
  · have hstep := count_succ_of_period hper (-(n : ℤ) - 1) hL c
    have hEq : (-(n : ℤ) - 1) + 1 = -(n : ℤ) := by ring
    rw [hEq] at hstep
    rw [← hstep]
    exact ih
