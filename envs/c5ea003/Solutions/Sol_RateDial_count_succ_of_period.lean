-- Prove2me | solution 1 for RateDial.count_succ_of_period
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:38:03.306891+00:00
-- url     : https://prove2.me/submissions/5e62f914-eb93-4d6a-81cb-8723c8d5d7d9

-- Sol generated from Shared/MixtureRateDialResidueCarriers.lean
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





omit [DecidableEq α] in
/-- Periodicity iterates. -/
theorem periodic_add_natMul {m : ℕ} {f : ℤ → α} (hper : PeriodicClass m f) (j : ℤ) :
    ∀ k : ℕ, f (j + m * k) = f j := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have harg : j + (m : ℤ) * ((n + 1 : ℕ) : ℤ) = (j + (m : ℤ) * (n : ℤ)) + (m : ℤ) := by
        push_cast; ring
      rw [harg, hper, ih]



/-! ## Quantitative version: window length not a multiple of the period -/




/-! ## Every residue-type carrier of `j` (and of `j² - N`) is periodic -/




/-! ## Capstone: no residue mixture removes any part of the excess -/







open RateDial in
theorem solution{m : ℕ} {f : ℤ → α} (hper : PeriodicClass m f) (a : ℤ)
    {L q : ℕ} (hL : L = m * q) (c : α) :
    count f (a + 1) L c = count f a L c := by
  classical
  set h : ℕ → ℕ := fun i => if f (a + i) = c then 1 else 0 with hh
  have e1 : ∑ i ∈ range (L + 1), h i = (∑ i ∈ range L, h (i + 1)) + h 0 :=
    Finset.sum_range_succ' h L
  have e2 : ∑ i ∈ range (L + 1), h i = (∑ i ∈ range L, h i) + h L :=
    Finset.sum_range_succ h L
  have e3 : h L = h 0 := by
    have hfa : f (a + (L : ℤ)) = f (a + ((0 : ℕ) : ℤ)) := by
      have harg : a + (L : ℤ) = a + (m : ℤ) * (q : ℤ) := by rw [hL]; push_cast; ring
      rw [harg, periodic_add_natMul hper a q]
      norm_num
    simp only [hh, hfa]
  have e4 : count f (a + 1) L c = ∑ i ∈ range L, h (i + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have harg : a + 1 + ((i : ℕ) : ℤ) = a + (((i + 1 : ℕ)) : ℤ) := by push_cast; ring
    simp only [hh, harg]
  have e5 : count f a L c = ∑ i ∈ range L, h i := rfl
  omega
