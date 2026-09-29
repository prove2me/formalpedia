-- Prove2me | solution 1 for Round11.zeroInfo_comp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:42:26.947399+00:00
-- url     : https://prove2.me/submissions/12bfeecf-317b-452e-b583-e8c048ff6c80

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
theorem solution{Ω : Finset α} {T : α → β} {S : α → γ} (g : β → δ)
    (h : ZeroInfo Ω T S) : ZeroInfo Ω (g ∘ T) S := by
  classical
  intro t' s
  set F := (Ω.image T).filter (fun t => g t = t') with hF
  have hmemF : ∀ t, t ∈ F ↔ ((∃ a ∈ Ω, T a = t) ∧ g t = t') := by
    intro t; rw [hF, Finset.mem_filter, Finset.mem_image]
  have h1 : (Ω.filter (fun w => (g ∘ T) w = t' ∧ S w = s)).card
      = ∑ t ∈ F, (Ω.filter (fun w => T w = t ∧ S w = s)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := T) (t := F) ?_]
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      have hgt : g t = t' := ((hmemF t).1 ht).2
      congr 1
      ext w
      simp only [mem_filter, Function.comp_apply]
      constructor
      · rintro ⟨⟨hw, _, hs⟩, hT⟩; exact ⟨hw, hT, hs⟩
      · rintro ⟨hw, hT, hs⟩
        exact ⟨⟨hw, by rw [hT, hgt], hs⟩, hT⟩
    · intro w hw
      have hw' := Finset.mem_filter.1 hw
      exact (hmemF (T w)).2 ⟨⟨w, hw'.1, rfl⟩, hw'.2.1⟩
  have h2 : (Ω.filter (fun w => (g ∘ T) w = t')).card
      = ∑ t ∈ F, (Ω.filter (fun w => T w = t)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := T) (t := F) ?_]
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      have hgt : g t = t' := ((hmemF t).1 ht).2
      congr 1
      ext w
      simp only [mem_filter, Function.comp_apply]
      constructor
      · rintro ⟨⟨hw, _⟩, hT⟩; exact ⟨hw, hT⟩
      · rintro ⟨hw, hT⟩
        exact ⟨⟨hw, by rw [hT, hgt]⟩, hT⟩
    · intro w hw
      have hw' := Finset.mem_filter.1 hw
      exact (hmemF (T w)).2 ⟨⟨w, hw'.1, rfl⟩, hw'.2⟩
  rw [h1, h2, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun t _ => h t s)
