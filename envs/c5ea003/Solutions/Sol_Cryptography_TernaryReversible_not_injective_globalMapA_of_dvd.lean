-- Prove2me | solution 1 for Cryptography.TernaryReversible.not_injective_globalMapA_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:08:45.790377+00:00
-- url     : https://prove2.me/submissions/f622175d-523a-4721-a3f3-267d9130f50b

-- Sol generated from Cryptography/TernaryReversible/Periodicity.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_General
import Theorems.Thm_Cryptography_TernaryReversible_injective_globalMapA_of_dvd

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
theorem solution{g : A → A → A → A} {m n : ℕ} (h : m ∣ n)
    (hm : ¬ Function.Injective (globalMapA (n := m) g)) :
    ¬ Function.Injective (globalMapA (n := n) g) :=
  fun hn => hm (injective_globalMapA_of_dvd h hn)
