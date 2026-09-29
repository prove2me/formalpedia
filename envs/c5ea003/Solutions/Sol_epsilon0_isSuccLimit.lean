-- Prove2me | solution 1 for epsilon0_isSuccLimit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:08:43.092786+00:00
-- url     : https://prove2.me/submissions/cb365f6d-f3c9-4164-bb72-b725b908f655

/-
# `epsilon0_isSuccLimit`
Target `a4fb79fc` (Open, not deprecated at draft time; re-read live immediately before submitting).

NOT YET COMPILED — drafted while the build lock was held by another ship.

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

The bundle defines `epsilon0 = Ordinal.nfp (omega0 ^ ·) 0`, the least fixed point of `a ↦ ω^a`
above `0`. This is exactly Mathlib's own characterisation of ε₀
(`Ordinal.epsilon_zero_eq_nfp : ε₀ = nfp (fun a ↦ ω ^ a) 0`), so the theory applies directly.

VERIFICATION IS SYMBOLIC, NOT NUMERIC — ordinals admit no floating-point check, so the argument
below IS the verification rather than a sketch of one:

  1. `a ↦ ω^a` is normal because `1 < ω`, so its least fixed point above 0 is genuinely fixed:
     `ω ^ epsilon0 = epsilon0`.
  2. `epsilon0 ≠ 0`, since a single iterate already gives `ω^0 = 1 ≤ epsilon0`.
  3. A power of a limit ordinal with nonzero exponent is a limit, so `ω ^ epsilon0` is a limit.
  4. Rewriting by the fixed point in (1) turns that into `epsilon0` being a limit.

PROBED, NOT GUESSED — every name below was read out of the vendored Mathlib source:
  * `Ordinal.nfp_fp (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a`
  * `Ordinal.isNormal_opow (a1 : 1 < a) : IsNormal (a ^ ·)`  (read off the proof term of
    `isSuccLimit_opow`, which is `(isNormal_opow a1).map_isSuccLimit`)
  * `Ordinal.isSuccLimit_opow_left (l : IsSuccLimit a) (hb : b ≠ 0) : IsSuccLimit (a ^ b)`
  * `Ordinal.isSuccLimit_omega0`, `Ordinal.one_lt_omega0`
  * `Ordinal.iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a`
-/
import Mathlib
import Definitions.Def_Evergreen_OmegaTower_Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Ordinal

/-- **The target, verbatim.** -/
theorem solution : Order.IsSuccLimit epsilon0 := by
  -- (1) the exponential base ω is normal, so epsilon0 is a genuine fixed point
  -- NB: `Ordinal.IsNormal` is declared `protected`, so `open Ordinal` does NOT bring the bare
  -- name into scope. The ascription is unnecessary anyway — `nfp_fp` infers it.
  have hnorm := isNormal_opow one_lt_omega0
  have hfp : omega0 ^ epsilon0 = epsilon0 := nfp_fp hnorm 0
  -- (2) one iterate already puts 1 below epsilon0, so it is nonzero
  have hone : (1 : Ordinal) ≤ epsilon0 := by
    have h := iterate_le_nfp (fun a : Ordinal => omega0 ^ a) 0 1
    simpa using h
  have hne : epsilon0 ≠ 0 := by
    intro h
    rw [h] at hone
    simp at hone
  -- (3) a power of a limit with nonzero exponent is a limit
  have hlim : Order.IsSuccLimit (omega0 ^ epsilon0) :=
    isSuccLimit_opow_left isSuccLimit_omega0 hne
  -- (4) and that power IS epsilon0
  rwa [hfp] at hlim
