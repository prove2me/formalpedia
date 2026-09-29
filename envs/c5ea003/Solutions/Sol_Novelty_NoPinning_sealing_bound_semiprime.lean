-- Prove2me | solution 1 for Novelty.NoPinning.sealing_bound_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:24:45.083994+00:00
-- url     : https://prove2.me/submissions/3619c108-c121-45b5-9793-ae2bfb89400b

-- Sol generated from Novelty/NoPinningSealing.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
import Theorems.Thm_Novelty_NoPinning_infinite_compensating_primes
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

/-- A prime candidate `p` can be excluded by the modulus-`L` data only if
`p ∣ L`: otherwise Dirichlet produces a compensating partner. -/
theorem excluded_dvd_modulus (L : ℕ) [NeZero L] {N₀ p : ℕ}
    (hN : Nat.Coprime N₀ L) (hp : p.Prime)
    (hexcl : ¬ ∃ q : ℕ, q.Prime ∧ p * q ≡ N₀ [MOD L]) : p ∣ L := by
  by_contra hdvd
  obtain ⟨q, hq, -, hmod⟩ :=
    (infinite_compensating_primes L hN ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd)).nonempty
  exact hexcl ⟨q, hq, hmod⟩

/-- If a finset of primes all divide `L ≠ 0`, then `2 ^ card ≤ L`. -/
theorem two_pow_card_le_of_dvd {L : ℕ} (hL : L ≠ 0) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ L) : 2 ^ S.card ≤ L := by
  have hsub : S ⊆ L.primeFactors := fun p hp =>
    Nat.mem_primeFactors.2 ⟨(hS p hp).1, (hS p hp).2, hL⟩
  calc 2 ^ S.card ≤ 2 ^ L.primeFactors.card :=
        Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card hsub)
    _ = ∏ _p ∈ L.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ L.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ L := Nat.le_of_dvd (Nat.pos_of_ne_zero hL) (Nat.prod_primeFactors_dvd L)

/-- **Sealing bound.**  A modulus-`L` battery that excludes `S.card` prime
candidates must have `2 ^ S.card ≤ L`: each excluded candidate costs a prime
factor of the modulus. -/
theorem two_pow_card_le_of_exclusion (L : ℕ) [NeZero L] {N₀ : ℕ}
    (hN : Nat.Coprime N₀ L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ ¬ ∃ q : ℕ, q.Prime ∧ p * q ≡ N₀ [MOD L]) :
    2 ^ S.card ≤ L :=
  two_pow_card_le_of_dvd (NeZero.ne L) fun p hp =>
    ⟨(hS p hp).1, excluded_dvd_modulus L hN (hS p hp).1 (hS p hp).2⟩

/-! ## The semiprime case -/

/-- A semiprime has at most two prime divisors. -/
theorem primes_dvd_semiprime_card_le {p₀ q₀ : ℕ} (hp : p₀.Prime) (hq : q₀.Prime)
    (X : ℕ) :
    ((Nat.primesBelow X).filter (fun p => p ∣ p₀ * q₀)).card ≤ 2 := by
  have hsub : (Nat.primesBelow X).filter (fun p => p ∣ p₀ * q₀) ⊆ {p₀, q₀} := by
    intro r hr
    obtain ⟨hrmem, hrdvd⟩ := Finset.mem_filter.1 hr
    have hrp : r.Prime := (Nat.mem_primesBelow.1 hrmem).2
    rcases (Nat.Prime.dvd_mul hrp).1 hrdvd with h | h
    · simp [(Nat.prime_dvd_prime_iff_eq hrp hp).1 h]
    · simp [(Nat.prime_dvd_prime_iff_eq hrp hq).1 h]
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _ |>.trans (by simp))




open Novelty.NoPinning in
theorem solution(L : ℕ) [NeZero L] {p₀ q₀ X : ℕ}
    (hp : p₀.Prime) (hq : q₀.Prime) (hN : Nat.Coprime (p₀ * q₀) L)
    (hexcl : ∀ p ∈ Nat.primesBelow X, ¬ p ∣ p₀ * q₀ →
      ¬ ∃ q : ℕ, q.Prime ∧ p * q ≡ p₀ * q₀ [MOD L]) :
    2 ^ ((Nat.primesBelow X).card - 2) ≤ L := by
  set S := (Nat.primesBelow X).filter (fun p => ¬ p ∣ p₀ * q₀) with hSdef
  have hcard : (Nat.primesBelow X).card - 2 ≤ S.card := by
    have hsplit :
        ((Nat.primesBelow X).filter (fun p => p ∣ p₀ * q₀)).card + S.card =
          (Nat.primesBelow X).card := by
      rw [hSdef]
      exact Finset.card_filter_add_card_filter_not (fun p => p ∣ p₀ * q₀)
    have := primes_dvd_semiprime_card_le hp hq X
    omega
  refine le_trans (Nat.pow_le_pow_right (by norm_num) hcard) ?_
  refine two_pow_card_le_of_exclusion L hN S fun p hp' => ?_
  obtain ⟨hmem, hndvd⟩ := Finset.mem_filter.1 hp'
  exact ⟨(Nat.mem_primesBelow.1 hmem).2, hexcl p hmem hndvd⟩
