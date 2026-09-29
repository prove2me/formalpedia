-- Prove2me | solution 1 for Novelty.NoPinning.infinite_compensating_primes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:17:43.122396+00:00
-- url     : https://prove2.me/submissions/f2ef54d9-63cb-4662-8ae6-68cdbff5fbcd

-- Sol generated from Novelty/NoPinningLemma.lean
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




/-! ## The pinned set is exactly the primes dividing `L` -/










open Novelty.NoPinning in
theorem solution(L : ℕ) [NeZero L] {N₀ p : ℕ}
    (hN : Nat.Coprime N₀ L) (hp : Nat.Coprime p L) :
    {q : ℕ | q.Prime ∧ Nat.Coprime q L ∧ p * q ≡ N₀ [MOD L]}.Infinite := by
  have hpu : IsUnit ((p : ZMod L)) := (ZMod.isUnit_iff_coprime p L).2 hp
  have hNu : IsUnit ((N₀ : ZMod L)) := (ZMod.isUnit_iff_coprime N₀ L).2 hN
  set u : (ZMod L)ˣ := hpu.unit with hu
  set a : ZMod L := ((u⁻¹ : (ZMod L)ˣ) : ZMod L) * (N₀ : ZMod L) with ha'
  have ha : IsUnit a := (Units.isUnit _).mul hNu
  refine (Nat.infinite_setOf_prime_and_eq_mod ha).mono ?_
  rintro q ⟨hq, hqa⟩
  have hqu : IsUnit ((q : ZMod L)) := by rw [hqa]; exact ha
  refine ⟨hq, (ZMod.isUnit_iff_coprime q L).1 hqu, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [hqa, ha']
  have hup : ((u : (ZMod L)ˣ) : ZMod L) = (p : ZMod L) := hpu.unit_spec
  calc (p : ZMod L) * (((u⁻¹ : (ZMod L)ˣ) : ZMod L) * (N₀ : ZMod L))
      = (((u : (ZMod L)ˣ) : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) * (N₀ : ZMod L) := by
        rw [hup]; ring
    _ = (N₀ : ZMod L) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
