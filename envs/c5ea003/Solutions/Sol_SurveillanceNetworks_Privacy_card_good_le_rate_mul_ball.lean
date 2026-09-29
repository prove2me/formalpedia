-- Prove2me | solution 1 for SurveillanceNetworks.Privacy.card_good_le_rate_mul_ball
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:33.807981+00:00
-- url     : https://prove2.me/submissions/498bd3d9-91c3-4f5b-a5b7-4892442d76e4

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
theorem solution(obs : S → M) (dec : M → S) (d : S → S → ℕ) (D B : ℕ)
    (G : Finset S)
    (hball : ∀ c : S, (univ.filter fun s => d c s ≤ D).card ≤ B)
    (hrec : ∀ s ∈ G, d (dec (obs s)) s ≤ D) :
    G.card ≤ rate obs * B := by
  have huniv : G = (G.image obs).biUnion (fun m => G.filter fun s => obs s = m) := by
    ext s; simp [Finset.mem_biUnion]; tauto
  rw [huniv]
  have hdisj : ∀ m₁ m₂, m₁ ≠ m₂ →
      Disjoint (G.filter fun s => obs s = m₁) (G.filter fun s => obs s = m₂) := by
    intro m₁ m₂ hne
    refine Finset.disjoint_left.mpr fun s hs₁ hs₂ => ?_
    simp at hs₁ hs₂
    exact hne (hs₁.2.symm.trans hs₂.2)
  rw [card_biUnion (fun m₁ _ m₂ _ hne => hdisj m₁ m₂ hne)]
  have hterm : ∀ u ∈ G.image obs, (G.filter fun s => obs s = u).card ≤ B := by
    intro u _
    have hsub : (G.filter fun s => obs s = u) ⊆ univ.filter fun s => d (dec u) s ≤ D := by
      intro s hs
      simp at hs
      have := hrec s hs.1
      rw [hs.2] at this
      simp [this]
    exact Nat.le_trans (Finset.card_mono hsub) (hball (dec u))
  calc ∑ u ∈ G.image obs, (G.filter fun s => obs s = u).card
      ≤ ∑ _u ∈ G.image obs, B := Finset.sum_le_sum hterm
    _ = (G.image obs).card * B := by simp [Finset.sum_const]
    _ ≤ (univ.image obs).card * B :=
        Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.image_subset_image (subset_univ G)))
    _ = rate obs * B := rfl
