-- Prove2me | Theorems.Thm_Novelty_NoPinning_infinite_compensating_primes
-- name    : Novelty.NoPinning.infinite_compensating_primes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:14:49.668894+00:00
-- url     : https://prove2.me/theorems/0ddf365b-972d-4834-aa8c-87e0bb044ba4
-- title:
--   Compensating-partner lemma.
-- statement:
--   **Compensating-partner lemma.**  Let `L ≥ 1`, let the target `N₀` and the
--   candidate `p` be coprime to `L`.  Then infinitely many primes `q` satisfy
--   `p · q ≡ N₀ (mod L)`; i.e. the candidate `p` can always be completed to a
--   semiprime carrying exactly the residue data of `N₀`.
--
--   The analytic input is Dirichlet's theorem: `N₀ p⁻¹` is a unit of `ZMod L`, and
--   every unit class contains infinitely many primes.
--
--   ```lean
--   theorem Novelty.NoPinning.infinite_compensating_primes(L : ℕ) [NeZero L] {N₀ p : ℕ}
--       (hN : Nat.Coprime N₀ L) (hp : Nat.Coprime p L) :
--       {q : ℕ | q.Prime ∧ Nat.Coprime q L ∧ p * q ≡ N₀ [MOD L]}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningLemma.lean#L70

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

theorem Novelty.NoPinning.infinite_compensating_primes(L : ℕ) [NeZero L] {N₀ p : ℕ}
    (hN : Nat.Coprime N₀ L) (hp : Nat.Coprime p L) :
    {q : ℕ | q.Prime ∧ Nat.Coprime q L ∧ p * q ≡ N₀ [MOD L]}.Infinite := by sorry
