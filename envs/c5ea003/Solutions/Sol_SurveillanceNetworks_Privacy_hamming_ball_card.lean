-- Prove2me | solution 1 for SurveillanceNetworks.Privacy.hamming_ball_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:34.819016+00:00
-- url     : https://prove2.me/submissions/b216407f-2455-46c2-affa-5207d799cf1a

-- Sol generated from Applications/SurveillanceNetworks/PrivacyThreshold.lean
import Mathlib
import Definitions.Def_Applications_SurveillanceNetworks_PrivacyThreshold
/-
# A sharp privacy threshold for surveillance of binary network histories

An observer watches a finite system whose configurations form a finite type `S`
(for a dynamic directed network on `n` participants observed for `T` time steps,
`S = (Fin T × Fin n × Fin n) → Bool`, a binary history tensor).  The observer
emits a *record* through a channel and a decoder later reconstructs a
configuration; the reconstruction error is measured by a dissimilarity
`d : S → S → ℕ` (Hamming distance on histories).

*Perfect privacy* means the record law does not depend on the configuration.
This file proves that perfect privacy has an exact geometric price:

* `privatelyAchievable_iff_exists_center` — a perfectly private **deterministic**
  channel meets the worst-case distortion budget `D` if and only if a single
  ball of radius `D` covers the whole configuration space.
* `randPrivatelyAchievable_iff_exists_center` — the same threshold holds for
  **randomized** channels (`S → PMF M`) whose output law is independent of the
  configuration, under an almost-sure worst-case distortion requirement:
  randomization does not help.
* `isLeast_privately_achievable` — consequently the optimal private worst-case
  distortion equals the covering radius of the one-codeword code,
  `coveringRadius d = ⨅_c ⨆_s d c s`.
* `hamming_coveringRadius` — for Hamming distortion on binary tensors indexed by
  a finite set `α` the covering radius is exactly `|α|`, so a perfectly private
  observer of a `T`-step network history on `n` nodes suffers worst-case
  distortion exactly `T * n * n` (`history_private_distortion`): privacy forces a
  totally uninformative reconstruction.

The complementary quantitative side is an exact-volume converse.  The fibres of a
channel are covered by distortion balls, giving `|S| ≤ rate · B`
(`card_le_rate_mul_ball`), and even a decoder allowed to fail outside a good set
`G` obeys `|G| ≤ rate · B` (`card_good_le_rate_mul_ball`).  For Hamming
distortion the ball volume is computed exactly,
`hamming_ball_card : |B(c, D)| = ∑_{i ≤ D} C(|α|, i)`, yielding the concrete
surveillance bound `hamming_rate_bound`:
`2 ^ |α| ≤ rate · ∑_{i ≤ D} C(|α|, i)`,
and its excess-distortion version `hamming_rate_bound_excess`.
-/

open Finset

open SurveillanceNetworks.Privacy

variable {S M : Type*}

/-! ## Privacy and distortion for deterministic channels -/




/-! ## Privacy and distortion for randomized channels -/





/-! ## The optimal private distortion is the covering radius -/





/-! ## Hamming distortion on binary tensors -/

variable {α : Type*} [Fintype α] [DecidableEq α]









/-! ## Exact covering converse -/

variable [Fintype S] [DecidableEq S] [DecidableEq M]








open SurveillanceNetworks.Privacy in
theorem solution(c : α → Bool) (D : ℕ) :
    (univ.filter fun s => hdist c s ≤ D).card
      = ∑ i ∈ range (D + 1), (Fintype.card α).choose i := by
  -- Define the Hamming ball and the sum
  set ball := univ.filter fun s => hdist c s ≤ D with hball
  set target := ∑ i ∈ range (D + 1), (Fintype.card α).choose i with htarget
  -- Define the map: s ↦ {i | c i ≠ s i}
  let f : (α → Bool) → Finset α := fun s => univ.filter fun i => c i ≠ s i
  -- f s has size = hdist c s
  have hf_size : ∀ s, (f s).card = hdist c s := fun s => rfl
  -- f is injective: if f s₁ = f s₂, then s₁ = s₂
  have hf_inj : ∀ s₁ s₂, f s₁ = f s₂ → s₁ = s₂ := by
    intro s₁ s₂ hf_eq
    funext i
    have hmem : i ∈ f s₁ ↔ i ∈ f s₂ := by rw [hf_eq]
    simp [f] at hmem
    cases hi : c i <;> cases hj : s₁ i <;> cases hk : s₂ i <;> simp_all
  -- The image of ball under f is {I : Finset α | I.card ≤ D}
  let subsets_le_D := Finset.biUnion (Finset.range (D + 1)) (fun i => Finset.powersetCard i (univ : Finset α))
  -- Show that f maps ball onto subsets_le_D
  have hf_image : ∀ I ∈ subsets_le_D, ∃ s, s ∈ ball ∧ f s = I := by
    intro I hI
    rw [Finset.mem_biUnion] at hI
    obtain ⟨k, hI_k, hI_mem⟩ := hI
    rw [Finset.mem_range] at hI_k
    rw [Finset.mem_powersetCard] at hI_mem
    -- Construct s that differs from c exactly at positions in I
    let s : α → Bool := fun a => if a ∈ I then !c a else c a
    use s
    constructor
    · -- Show s ∈ ball
      simp only [ball, hdist, Finset.mem_filter, Finset.mem_univ, true_and]
      have hcard : (univ.filter fun i => c i ≠ s i).card = #I := by
        congr 1
        ext i
        simp [s]
      rw [hcard, hI_mem.2]
      exact Nat.lt_succ_iff.mp hI_k
    · -- Show f s = I
      ext i
      simp [f, s]
  -- f maps ball into subsets_le_D
  have hf_maps : ∀ s ∈ ball, f s ∈ subsets_le_D := by
    intro s hs
    rw [Finset.mem_biUnion]
    refine ⟨(f s).card, ?_, ?_⟩
    · simp only [Finset.mem_range]
      rw [hf_size]
      exact Nat.lt_succ_of_le (by simpa [ball] using hs)
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, rfl⟩
  -- Use Finset.card_bij to show card ball = card subsets_le_D
  have hbij : ball.card = subsets_le_D.card := by
    apply Finset.card_bij (fun s _ => f s)
    · intro s hs
      exact hf_maps s hs
    · intro s₁ hs₁ s₂ hs₂ heq
      exact hf_inj s₁ s₂ heq
    · intro I hI
      obtain ⟨s, hs, hf_eq⟩ := hf_image I hI
      exact ⟨s, hs, hf_eq⟩
  -- Compute card subsets_le_D
  have hcard_subsets : subsets_le_D.card = ∑ i ∈ Finset.range (D + 1), Nat.choose (Fintype.card α) i := by
    show (Finset.biUnion (Finset.range (D + 1)) (fun i => Finset.powersetCard i (univ : Finset α))).card = ∑ i ∈ Finset.range (D + 1), Nat.choose (Fintype.card α) i
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_powersetCard, Finset.card_univ]
    · intro i hi j hj hij
      simp only [Finset.disjoint_left, Finset.mem_powersetCard]
      intro I ⟨hI_sub, hI_card⟩ ⟨hI_sub', hI_card'⟩
      exact hij (hI_card.symm.trans hI_card')
  rw [hbij, hcard_subsets, htarget]
