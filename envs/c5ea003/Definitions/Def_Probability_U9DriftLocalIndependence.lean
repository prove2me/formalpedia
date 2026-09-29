-- Prove2me | Definitions.Def_Probability_U9DriftLocalIndependence
-- name    : Probability_U9DriftLocalIndependence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:42.111984+00:00
-- url     : https://prove2.me/theorems/720a1a2c-461e-4add-826f-150e5cf6b096
-- title:
--   Aether Catalog definitions — Probability_U9DriftLocalIndependence
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftLocalIndependence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftLocalIndependence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_U9DriftLocalDensity
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

namespace U9Drift

open Finset

/-! ## The CRT isomorphism is reduction -/




/-! ## Counting the survivors at one prime -/

/-- The number of residues `j mod p` at which `p ∤ j² - N`. -/
noncomputable def missCount (p : ℕ) (N : ℤ) : ℕ :=
  Nat.card {x : ZMod p // ¬ x ^ 2 = (N : ZMod p)}





/-! ## Exact independence -/




/-! ## Densities -/

/-- The local survival density at `p`: the density of `j` with `p ∤ j² - N`. -/
noncomputable def missDensity (p : ℕ) (N : ℤ) : ℚ := (missCount p N : ℚ) / p




end U9Drift


