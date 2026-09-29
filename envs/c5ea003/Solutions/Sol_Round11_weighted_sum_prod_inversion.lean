-- Prove2me | solution 1 for Round11.weighted_sum_prod_inversion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:42:26.35917+00:00
-- url     : https://prove2.me/submissions/0c4c9055-a862-4bf2-ad73-e58d1c1267de

-- Sol generated from Combinatorics/Round11FingerprintInformation.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Definitions.Def_Combinatorics_Round11FingerprintInformation
/-
# Round-11 Closures, Part III: CFSIGMA — the hint feed is starved

Formal companion to the round-11 negative-results synthesis
(`29_Round11_Closures.md`, hypothesis **CFSIGMA**).

The paper's central claim is that the Coppersmith hint-amplification channel
*exists* — an approximation `σ̂ ≈ p + q` is worth a factorization — but that the
cycle-index fingerprint provides *no source* for it: below the order scale the
fingerprint carries zero mutual information with `(p+q) mod ℓ`.

This file proves both halves in an exact, finitary form.

* **The channel exists.**  `Round11.sum_prod_inversion`: the pair `(p+q, p·q)`
  determines `{p, q}`.  An *exact* hint `σ = p + q` is literally a factorization.
* **The source is starved.**  We use the finitary (counting) notion of
  independence `Round11.ZeroInfo`: a statistic `T` is uninformative about a
  secret `S` on a finite instance set `Ω` when every joint fibre has exactly the
  product cardinality.  `Round11.cfsigma_starved` shows that the *truncated
  fingerprint* `c ↦ F(c)`, `1 ≤ c ≤ D`, restricted to instances whose two
  multiplicative orders exceed `D`, is uninformative about `(p+q) mod ℓ` — for
  **every** modulus `ℓ` and **every** instance set.  By the data-processing
  lemma `Round11.zeroInfo_comp`, no post-processing of the truncated fingerprint
  can do better (`Round11.cfsigma_starved_postprocessed`).

The proof of starvation is Part I's order seal: below the order scale the
fingerprint is a *constant* function of the instance, so its fibres are either
empty or all of `Ω`.  Non-vacuity of the hypothesis is witnessed by
`Round11.cfsigma_instance_witness`.
-/

open Round11

open Finset

/-! ## The channel: an exact sum hint is a factorization -/




/-! ## Finitary independence -/

variable {α β γ δ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq δ]




/-! ## The truncated fingerprint and the CFSIGMA closure -/











/-! ## Non-vacuity -/






open Round11 in
theorem solution{A B p q p' q' N : ℕ}
    (h : p * q = N) (h' : p' * q' = N) (hlin : A * p + B * q = A * p' + B * q') :
    p = p' ∨ A * p * p' = B * N := by
  have hz : ((p:ℤ) - p') * ((A:ℤ) * (p + p') - ((A:ℤ) * p + (B:ℤ) * q)) = 0 := by
    have hZ : (p:ℤ) * q = N := by exact_mod_cast h
    have hZ' : (p':ℤ) * q' = N := by exact_mod_cast h'
    have hL : (A:ℤ) * p + B * q = (A:ℤ) * p' + B * q' := by exact_mod_cast hlin
    nlinarith [hZ, hZ', hL]
  rcases mul_eq_zero.1 hz with hc | hc
  · left; omega
  · right
    have hZ : (p:ℤ) * q = N := by exact_mod_cast h
    have hfin : (A:ℤ) * p * p' = B * N := by nlinarith [hc, hZ]
    exact_mod_cast hfin
