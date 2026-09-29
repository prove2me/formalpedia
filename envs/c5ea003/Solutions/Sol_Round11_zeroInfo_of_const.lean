-- Prove2me | solution 1 for Round11.zeroInfo_of_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:56:28.823381+00:00
-- url     : https://prove2.me/submissions/7e47da73-4ca4-487e-8082-f1f528e6ce6c

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
theorem solution{Ω : Finset α} {T : α → β} {S : α → γ} {t₀ : β}
    (h : ∀ w ∈ Ω, T w = t₀) : ZeroInfo Ω T S := by
  intro t s
  by_cases ht : t = t₀
  · subst ht
    have e1 : Ω.filter (fun w => T w = t ∧ S w = s) = Ω.filter (fun w => S w = s) :=
      Finset.filter_congr (fun w hw => by simp [h w hw])
    have e2 : Ω.filter (fun w => T w = t) = Ω :=
      Finset.filter_true_of_mem (fun w hw => h w hw)
    rw [e1, e2, mul_comm]
  · have e1 : Ω.filter (fun w => T w = t ∧ S w = s) = ∅ :=
      Finset.filter_false_of_mem (fun w hw hc => ht (by rw [← hc.1, h w hw]))
    have e2 : Ω.filter (fun w => T w = t) = ∅ :=
      Finset.filter_false_of_mem (fun w hw hc => ht (by rw [← hc, h w hw]))
    rw [e1, e2]
    simp
