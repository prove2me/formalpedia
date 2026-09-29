-- Prove2me | Theorems.Thm_Novelty_NoPinning_isModObs_residue_self
-- name    : Novelty.NoPinning.isModObs_residue_self
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:15:40.035618+00:00
-- url     : https://prove2.me/theorems/af2c2eb5-0827-44c5-ac2b-e55bba8ebda4
-- title:
--   The finest observable of modulus `L`: the residue itself.
-- statement:
--   The finest observable of modulus `L`: the residue itself.
--
--   ```lean
--   theorem Novelty.NoPinning.isModObs_residue_self(L : ℕ) : IsModObs L (fun N => N % L) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningLemma.lean#L51

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

theorem Novelty.NoPinning.isModObs_residue_self(L : ℕ) : IsModObs L (fun N => N % L) := by sorry
