-- Prove2me | solution 1 for Cryptography.TernaryReversible.bijective_iff_injective_globalMapA
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:47.44618+00:00
-- url     : https://prove2.me/submissions/074d37a8-3bb1-4524-9c51-3c334a7230ae

-- Sol generated from Cryptography/TernaryReversible/Periodicity.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_General

/-!
# Divisor monotonicity of cycle injectivity, and a factorial test

Cycle-bijectivity is a statement about *all* cycle lengths at once, so it is a priori an
infinite test.  This file isolates the first genuinely structural reduction of that test:
the lengths at which a radius-one rule fails to be injective form a set that is **closed
upwards under divisibility**.

The mechanism is that the reduction map `π : ZMod n → ZMod m` (for `m ∣ n`) is a
*surjective ring homomorphism*, hence commutes with the shifts `i ↦ i ± 1` that define the
global map.  Consequently `s ∘ π` is a configuration on the long cycle whose image under
the global map is the pull-back of the image of `s`:

`globalMapA g (s ∘ π) = (globalMapA g s) ∘ π`  (`globalMapA_castHom`).

Two distinct configurations on the short cycle therefore lift to two distinct
configurations on the long cycle with the same image, and non-injectivity propagates from
`m` to every multiple of `m`.

## Main results

* `globalMapA_castHom` — the intertwining identity for the reduction map;
* `injective_globalMapA_of_dvd` — injectivity at `n` implies injectivity at every divisor
  of `n`;
* `not_injective_globalMapA_of_dvd` — its contrapositive: failure propagates to multiples;
* `cycleBijectiveA_iff_factorial` — cycle-bijectivity is equivalent to injectivity on the
  *cofinal divisibility chain* of factorial lengths `1!, 2!, 3!, …`;
* `diag_injective_of_injective_at` — a single cycle length already forces the diagonal map
  `b ↦ g b b b` to be injective (the length-`1` divisor).
-/

open Cryptography
open TernaryReversible

variable {A : Type}

/-! ## The reduction map intertwines the global maps -/




/-! ## A cofinal chain of test lengths -/




/-! ## The length-one divisor -/



open Cryptography.TernaryReversible in
theorem solution[Fintype A] (g : A → A → A → A) {n : ℕ}
    (hn : 0 < n) :
    Function.Bijective (globalMapA (n := n) g) ↔ Function.Injective (globalMapA (n := n) g) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  exact ⟨fun h => h.1, fun h => Finite.injective_iff_bijective.1 h⟩
