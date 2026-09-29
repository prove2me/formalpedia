-- Prove2me | solution 1 for RainbowAP.sum_choose_missCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:24:02.438437+00:00
-- url     : https://prove2.me/submissions/eb25d8c2-1553-457f-9c54-5d32bd36a8aa

-- Sol generated from Shared/RainbowAPHigherMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Theorems.Thm_RainbowAP_mem_missing

/-!
# All binomial moments of the missed-letter count

The first and second moment identities of `Shared.RainbowAPSpectrumMoments` are the cases
`r = 1, 2` of a single exact identity: for every `r`,

  `∑_{f : Fin m → α} C(missCount f, r) = C(N, r) · (N - r) ^ m`,  `N = |α|`.

Equivalently, the `r`-th binomial moment of the number of missed letters of a uniformly random
word is `C(N,r)(1 - r/N)^m`, which is the moment sequence of a Poisson variable of mean
`N (1-1/N)^m` in the limit.  This is the exact combinatorial input needed for a Poisson limit
law of the full-spectrum transition.
-/

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Words of length `m` avoiding every letter of a fixed set `S`. -/
lemma card_avoid_set (m : ℕ) (S : Finset α) :
    ((univ : Finset (Fin m → α)).filter (fun f => ∀ x, f x ∉ S)).card
      = (Fintype.card α - S.card) ^ m := by
  have h1 : ((univ : Finset (Fin m → α)).filter (fun f => ∀ x, f x ∉ S))
      = Fintype.piFinset (fun _ : Fin m => (univ \ S)) := by
    ext f
    simp [Fintype.mem_piFinset]
  have h2 : ((univ \ S : Finset α)).card = Fintype.card α - S.card := by
    simp [Finset.card_sdiff, Finset.card_univ]
  rw [h1, Fintype.card_piFinset]
  simp [h2]

lemma subset_missing_iff {m : ℕ} (f : Fin m → α) (S : Finset α) :
    S ⊆ missing f ↔ ∀ x, f x ∉ S := by
  constructor
  · intro hS x hx
    have := hS hx
    rw [mem_missing] at this
    exact this x rfl
  · intro h a ha
    rw [mem_missing]
    intro x hx
    exact h x (hx ▸ ha)






open RainbowAP in
theorem solution(r m : ℕ) :
    ∑ f : Fin m → α, (missCount f).choose r
      = (Fintype.card α).choose r * (Fintype.card α - r) ^ m := by
  have key : ∀ f : Fin m → α, (missCount f).choose r
      = ∑ S ∈ Finset.powersetCard r (univ : Finset α),
          (if S ⊆ missing f then 1 else 0) := by
    intro f
    rw [missCount, ← Finset.card_powersetCard]
    rw [Finset.card_filter (fun S => S ⊆ missing f) (Finset.powersetCard r univ) |>.symm]
    congr 1
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Finset.subset_univ S, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩
      exact ⟨h1, h2⟩
  simp_rw [key]
  rw [Finset.sum_comm]
  have step : ∀ S ∈ Finset.powersetCard r (univ : Finset α),
      (∑ f : Fin m → α, (if S ⊆ missing f then 1 else 0))
        = (Fintype.card α - r) ^ m := by
    intro S hS
    have hcard : S.card = r := (Finset.mem_powersetCard.1 hS).2
    rw [← Finset.card_filter]
    have : ((univ : Finset (Fin m → α)).filter (fun f => S ⊆ missing f))
        = ((univ : Finset (Fin m → α)).filter (fun f => ∀ x, f x ∉ S)) := by
      apply Finset.filter_congr
      intro f _
      simp [subset_missing_iff f S]
    rw [this, card_avoid_set m S, hcard]
  rw [Finset.sum_congr rfl step, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, smul_eq_mul]
