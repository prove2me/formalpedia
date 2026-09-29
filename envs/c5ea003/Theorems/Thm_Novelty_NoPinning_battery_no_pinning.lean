-- Prove2me | Theorems.Thm_Novelty_NoPinning_battery_no_pinning
-- name    : Novelty.NoPinning.battery_no_pinning
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:15:13.763239+00:00
-- url     : https://prove2.me/theorems/26ab000e-7f49-48e3-9c9b-591b562334c5
-- title:
--   Finite-battery form of the no-pinning lemma: the entire battery of ℤ-valued
-- statement:
--   Finite-battery form of the no-pinning lemma: the entire battery of ℤ-valued
--   observables agrees on `p·q` and `N₀`, for infinitely many primes `q`.
--
--   ```lean
--   theorem Novelty.NoPinning.battery_no_pinning(L : ℕ) [NeZero L] (h2 : 2 ∣ L)
--       (Bat : List (ℕ → ℤ)) (hBat : ∀ f ∈ Bat, IsModObs L f) {N₀ p : ℕ}
--       (hN : Nat.Coprime N₀ L) (hp : Nat.Coprime p L) :
--       {q : ℕ | q.Prime ∧ batteryValue Bat (p * q) = batteryValue Bat N₀}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningLemma.lean#L122

-- Thm stub generated from Novelty/NoPinningLemma.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
/-
# The Class-Wide No-Pinning Lemma

Phase A research file (Novelty domain).  This file generalises the
`Bridges.ResidueLeakage` Dirichlet no-pruning theorem (QRLEAK, Jacobi symbols
only) to the **entire class of modulus-`L` observables**: every predicate of a
semiprime `N` that can be evaluated from `N mod L` alone.  For
`L = 4 · lcm(1,…,B)` with `B = poly(log N)` this class contains

* all residues `N mod m` with `m ≤ B`,
* all Jacobi symbols `(a | N)` with `4a ∣ L`,
* all gcds `gcd(N, c)` with `c ∣ L` (and, by the barrier-1 lemma
  `gcd(f(N), N) = gcd(f(0), N)`, all polynomial gcds too).

## Setting

An *observable of modulus `L`* is any map `f : ℕ → β` with
`f m = f n` whenever `m` and `n` are odd and congruent mod `L`
(`IsModObs`).  A *battery* is a finite list of ℤ-valued observables.

## Main results

* `infinite_compensating_primes` — **the Dirichlet core**: for a target `N₀`
  and a candidate `p`, both coprime to `L`, there are infinitely many primes
  `q ≡ N₀ p⁻¹ (mod L)`; each of them satisfies `p·q ≡ N₀ (mod L)`.
* `no_pinning_universal` — **the class-wide no-pinning lemma**: for infinitely
  many primes `q`, *every* observable of modulus `L`, in *every* value type,
  agrees on `p·q` and on `N₀`.  A poly(log N)-computable congruence battery
  therefore never eliminates the candidate `p`.
* `battery_no_pinning` — the finite-battery form.
* `compensable_iff_not_dvd` — **exact description of the pinned set**: a prime
  `p` is eliminated by the modulus-`L` data if and only if `p ∣ L`.
* `pinnedPrimes_card_le_log` — the pinned set has at most `log₂ L` elements,
  and `unpinnedPrimes_infinite` — its complement inside the primes is infinite.
* `no_pinning_large_primes` — the ambiguity is not confined to small numbers:
  for every bound `M` there is a semiprime `p·q` with `p, q > M` carrying the
  same modulus-`L` data as `N₀`.
-/


open Novelty.NoPinning

/-! ## Observables of a fixed modulus -/





/-! ## Elementary coprimality facts -/


/-! ## The Dirichlet core: compensating primes exist -/


/-! ## The class-wide no-pinning lemma -/

theorem Novelty.NoPinning.battery_no_pinning(L : ℕ) [NeZero L] (h2 : 2 ∣ L)
    (Bat : List (ℕ → ℤ)) (hBat : ∀ f ∈ Bat, IsModObs L f) {N₀ p : ℕ}
    (hN : Nat.Coprime N₀ L) (hp : Nat.Coprime p L) :
    {q : ℕ | q.Prime ∧ batteryValue Bat (p * q) = batteryValue Bat N₀}.Infinite := by sorry
