-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_not_injective_globalMapA_of_dvd
-- name    : Cryptography.TernaryReversible.not_injective_globalMapA_of_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:45:59.668076+00:00
-- url     : https://prove2.me/theorems/c75bcfac-59bc-4975-aa37-4ccdaf15c891
-- title:
--   Contrapositive form: a failure of injectivity on the cycle of length `m` propagates to
-- statement:
--   Contrapositive form: a failure of injectivity on the cycle of length `m` propagates to
--   **every** multiple of `m`.  In particular a single bad length produces infinitely many.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.not_injective_globalMapA_of_dvd{g : A → A → A → A} {m n : ℕ} (h : m ∣ n)
--       (hm : ¬ Function.Injective (globalMapA (n := m) g)) :
--       ¬ Function.Injective (globalMapA (n := n) g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/Periodicity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/Periodicity.lean#L63

-- Thm stub generated from Cryptography/TernaryReversible/Periodicity.lean
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

theorem Cryptography.TernaryReversible.not_injective_globalMapA_of_dvd{g : A → A → A → A} {m n : ℕ} (h : m ∣ n)
    (hm : ¬ Function.Injective (globalMapA (n := m) g)) :
    ¬ Function.Injective (globalMapA (n := n) g) := by sorry
