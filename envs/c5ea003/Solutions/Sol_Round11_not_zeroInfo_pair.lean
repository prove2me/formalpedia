-- Prove2me | solution 1 for Round11.not_zeroInfo_pair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:59:48.278126+00:00
-- url     : https://prove2.me/submissions/e34232eb-bb25-40c8-b256-cd660db7a10b

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
theorem solution[DecidableEq α] {T : α → β} {S : α → γ} {w₁ w₂ : α}
    (hne : w₁ ≠ w₂) (hT : T w₁ ≠ T w₂) (hS : S w₁ ≠ S w₂) :
    ¬ ZeroInfo ({w₁, w₂} : Finset α) T S := by
  intro h
  have h2 := h (T w₁) (S w₁)
  rw [show ({w₁, w₂} : Finset α).filter (fun w => T w = T w₁ ∧ S w = S w₁) = {w₁} by
        simp [Finset.filter_insert, Finset.filter_singleton, hT.symm, hS.symm],
      show ({w₁, w₂} : Finset α).filter (fun w => T w = T w₁) = {w₁} by
        simp [Finset.filter_insert, Finset.filter_singleton, hT.symm],
      show ({w₁, w₂} : Finset α).filter (fun w => S w = S w₁) = {w₁} by
        simp [Finset.filter_insert, Finset.filter_singleton, hS.symm],
      Finset.card_singleton, Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton] at h2
  omega
