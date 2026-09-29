-- Prove2me | Theorems.Thm_U9Drift_local_independence_prod
-- name    : U9Drift.local_independence_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:22:34.85117+00:00
-- url     : https://prove2.me/theorems/a6ca4fb9-6756-4e25-a138-4e2e57f1d696
-- title:
--   Exact local independence for a finite set of pairwise coprime moduli.
-- statement:
--   **Exact local independence for a finite set of pairwise coprime moduli.**  The survivor
--   count modulo `∏ p` is the product of the local survivor counts.  This is the entire
--   multiplicative content of the sieve model: it is a theorem, not a heuristic.  What remains
--   heuristic is only the passage from a finite prime set to genuine smoothness.
--
--   ```lean
--   theorem U9Drift.local_independence_prod(N : ℤ) :
--       ∀ S : Finset ℕ, (S : Set ℕ).Pairwise Nat.Coprime → ∀ M : ℕ, M = ∏ p ∈ S, p →
--         Nat.card {j : ZMod M // ∀ p ∈ S, ¬ (ZMod.cast j : ZMod p) ^ 2 = (N : ZMod p)}
--           = ∏ p ∈ S, missCount p N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/U9DriftLocalIndependence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/U9DriftLocalIndependence.lean#L123

-- Thm stub generated from Probability/U9DriftLocalIndependence.lean
import Mathlib
import Definitions.Def_Probability_U9DriftLocalDensity
import Definitions.Def_Probability_U9DriftLocalIndependence
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# The local conditions at distinct primes are *exactly* independent

Context (experiment 569, paper 216).  The smoothness model behind the band-9 study is
multiplicative: the chance that `j² - N` survives sieving by a set of small primes is taken
to be the product of the per-prime survival chances.  For the *local* (residue-counting)
part of that model this is not a heuristic at all — it is the Chinese remainder theorem.
This file proves it, and thereby isolates exactly which step of the Dickman-style argument
is still a heuristic (the passage from a finite prime set to full smoothness, not the
independence of the individual congruence conditions).

Main results:

* `U9Drift.chineseRemainder_fst` / `U9Drift.chineseRemainder_snd` — the CRT isomorphism is
  the pair of reduction maps, so a condition on the two components is exactly a pair of
  congruence conditions.
* `U9Drift.missCount_eq` — the number of residues `j mod p` with `p ∤ j² - N` is
  `p - (1 + legendreSym p N)`.
* `U9Drift.local_independence` — for coprime moduli the joint survivor count factors as the
  product of the two local survivor counts, with no error term.
* `U9Drift.local_independence_prod` — the same for an arbitrary finite set of pairwise
  coprime moduli: the survivor count modulo `∏ p` is `∏ (survivor count mod p)`.
* `U9Drift.missDensity_mul` — equivalently, the survival densities multiply exactly.
* `U9Drift.missDensity_eq_one_sub` / `U9Drift.missDensity_sub_control` — each factor is
  `1 - (1 + legendreSym p N)/p`, so the candidate pool's local survival probability differs
  from the control's `1 - 1/p` by exactly `legendreSym p N / p`, of either sign.
-/

open U9Drift

open Finset

/-! ## The CRT isomorphism is reduction -/




/-! ## Counting the survivors at one prime -/






/-! ## Exact independence -/

theorem U9Drift.local_independence_prod(N : ℤ) :
    ∀ S : Finset ℕ, (S : Set ℕ).Pairwise Nat.Coprime → ∀ M : ℕ, M = ∏ p ∈ S, p →
      Nat.card {j : ZMod M // ∀ p ∈ S, ¬ (ZMod.cast j : ZMod p) ^ 2 = (N : ZMod p)}
        = ∏ p ∈ S, missCount p N := by sorry
