-- Prove2me | solution 1 for Cryptography.TernaryReversible.injective_globalMapA_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:51.374581+00:00
-- url     : https://prove2.me/submissions/53694f2c-e9e1-41a0-8389-172dd040b4b1

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

/-- For `m ∣ n` the reduction `π : ZMod n → ZMod m` is a ring homomorphism, so it commutes
with the two shifts occurring in the global map: pulling a configuration back along `π`
pulls its image back along `π` as well. -/
theorem globalMapA_castHom (g : A → A → A → A) {m n : ℕ} (h : m ∣ n) (s : ZMod m → A) :
    globalMapA g (s ∘ (ZMod.castHom h (ZMod m))) =
      (globalMapA g s) ∘ (ZMod.castHom h (ZMod m)) := by
  funext i
  simp only [globalMapA, Function.comp_apply, map_sub, map_add, map_one]



/-! ## A cofinal chain of test lengths -/




/-! ## The length-one divisor -/



open Cryptography.TernaryReversible in
theorem solution{g : A → A → A → A} {m n : ℕ} (h : m ∣ n)
    (hn : Function.Injective (globalMapA (n := n) g)) :
    Function.Injective (globalMapA (n := m) g) := by
  intro s t hst
  set π := ZMod.castHom h (ZMod m) with hπ
  have hlift : globalMapA (n := n) g (s ∘ π) = globalMapA (n := n) g (t ∘ π) := by
    rw [globalMapA_castHom g h s, globalMapA_castHom g h t, hst]
  have hcomp : s ∘ π = t ∘ π := hn hlift
  funext j
  obtain ⟨i, rfl⟩ := ZMod.castHom_surjective h j
  exact congrFun hcomp i
