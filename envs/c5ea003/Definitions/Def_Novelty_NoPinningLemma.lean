-- Prove2me | Definitions.Def_Novelty_NoPinningLemma
-- name    : Novelty_NoPinningLemma
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:38.888275+00:00
-- url     : https://prove2.me/theorems/1b3f212a-bf5c-433f-b8ce-1e7141e248ef
-- title:
--   Aether Catalog definitions — Novelty_NoPinningLemma
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NoPinningLemma`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NoPinningLemma.lean by skeleton subtraction
import Mathlib
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


namespace Novelty.NoPinning

/-! ## Observables of a fixed modulus -/

/-- `IsModObs L f`: the observable `f` is a function of `N mod L` on odd inputs.
This is exactly the class of predicates a `poly(log N)`-time congruence battery
with modulus `L` can evaluate. -/
def IsModObs (L : ℕ) {β : Type} (f : ℕ → β) : Prop :=
  ∀ ⦃m n : ℕ⦄, Odd m → Odd n → m ≡ n [MOD L] → f m = f n


/-- The value of a battery (a finite list of ℤ-valued observables) at `N`. -/
def batteryValue (Bat : List (ℕ → ℤ)) (N : ℕ) : List ℤ := Bat.map (fun f => f N)


/-! ## Elementary coprimality facts -/


/-! ## The Dirichlet core: compensating primes exist -/


/-! ## The class-wide no-pinning lemma -/




/-! ## The pinned set is exactly the primes dividing `L` -/



/-- The set of pinned candidates: primes dividing the modulus. -/
def pinnedPrimes (L : ℕ) : Finset ℕ := L.primeFactors






end Novelty.NoPinning


