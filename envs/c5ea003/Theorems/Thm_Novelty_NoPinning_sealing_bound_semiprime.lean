-- Prove2me | Theorems.Thm_Novelty_NoPinning_sealing_bound_semiprime
-- name    : Novelty.NoPinning.sealing_bound_semiprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:16:07.307455+00:00
-- url     : https://prove2.me/theorems/fbd2ae5f-834a-44a8-8acc-fa1542164834
-- title:
--   The sealing theorem for semiprimes.
-- statement:
--   **The sealing theorem for semiprimes.**  Let `N₀ = p₀·q₀` be a semiprime
--   coprime to `L`, and suppose the modulus-`L` battery excludes *every* prime
--   candidate below `X` except the two genuine factors.  Then
--
--   `2 ^ (π(X) − 2) ≤ L`,
--
--   where `π(X) = (Nat.primesBelow X).card`.  A factoring search must exclude
--   candidates up to `X ≈ √N₀`, so the modulus of a pinning battery is
--   `exp(Ω(√N₀ / log N₀))` — never `poly(log N₀)`.
--
--   ```lean
--   theorem Novelty.NoPinning.sealing_bound_semiprime(L : ℕ) [NeZero L] {p₀ q₀ X : ℕ}
--       (hp : p₀.Prime) (hq : q₀.Prime) (hN : Nat.Coprime (p₀ * q₀) L)
--       (hexcl : ∀ p ∈ Nat.primesBelow X, ¬ p ∣ p₀ * q₀ →
--         ¬ ∃ q : ℕ, q.Prime ∧ p * q ≡ p₀ * q₀ [MOD L]) :
--       2 ^ ((Nat.primesBelow X).card - 2) ≤ L := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningSealing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningSealing.lean#L100

-- Thm stub generated from Novelty/NoPinningSealing.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
/-
# Sealing: what a battery must pay in order to pin

Companion to `Novelty/NoPinningLemma.lean`.  The no-pinning lemma says a
modulus-`L` battery eliminates only the primes dividing `L`.  Here we turn this
around into a *lower bound on the modulus* of any battery that does prune, which
is the quantitative form of the "sealed" side of the barrier programme.

## Main results

* `isModObs_iff_mod_reduction` — **universality of the residue channel**: for
  even `L`, an observable has modulus `L` iff it factors through `N ↦ N mod L`.
  No cleverer poly(log N) congruence predicate exists at a given modulus.
* `excluded_dvd_modulus` — a prime candidate can be excluded only if it divides
  the modulus.
* `two_pow_card_le_of_exclusion` — **sealing bound**: if a modulus-`L` battery
  excludes `k` prime candidates then `2 ^ k ≤ L`, i.e. `k ≤ log₂ L`.
* `sealing_bound_semiprime` — for a semiprime target `N₀ = p₀·q₀`, a battery
  that excludes every prime candidate below `X` (other than the two true
  factors) must have modulus `L ≥ 2 ^ (π(X) − 2)`.  Since a factorisation search
  needs `X ≈ √N`, the modulus — hence the description length of the battery — is
  exponential in `√N / log N`: no poly(log N) battery can do it.
* `poly_battery_cannot_seal` — contrapositive slogan form: a battery whose
  modulus is bounded by `2 ^ k` leaves at least `π(X) − 2 − k` prime candidates
  below `X` alive.
-/


open Novelty.NoPinning

/-! ## Universality of the residue channel -/


/-! ## Exclusion forces divisibility -/




/-! ## The semiprime case -/

theorem Novelty.NoPinning.sealing_bound_semiprime(L : ℕ) [NeZero L] {p₀ q₀ X : ℕ}
    (hp : p₀.Prime) (hq : q₀.Prime) (hN : Nat.Coprime (p₀ * q₀) L)
    (hexcl : ∀ p ∈ Nat.primesBelow X, ¬ p ∣ p₀ * q₀ →
      ¬ ∃ q : ℕ, q.Prime ∧ p * q ≡ p₀ * q₀ [MOD L]) :
    2 ^ ((Nat.primesBelow X).card - 2) ≤ L := by sorry
