-- Prove2me | Theorems.Thm_SurveillanceNetworks_Privacy_card_le_rate_mul_ball
-- name    : SurveillanceNetworks.Privacy.card_le_rate_mul_ball
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:04:31.345682+00:00
-- url     : https://prove2.me/theorems/ba12af84-4dae-4c74-9e4d-494201657faf
-- title:
--   Covering converse.
-- statement:
--   **Covering converse.**  If a decoder reconstructs every configuration within
--   distortion `D`, and every ball of radius `D` has at most `B` elements, then the
--   channel must emit at least `|S| / B` records.
--
--   ```lean
--   theorem SurveillanceNetworks.Privacy.card_le_rate_mul_ball(obs : S → M) (dec : M → S) (d : S → S → ℕ) (D B : ℕ)
--       (hball : ∀ c : S, (univ.filter fun s => d c s ≤ D).card ≤ B)
--       (hrec : ∀ s, d (dec (obs s)) s ≤ D) :
--       Fintype.card S ≤ rate obs * B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/SurveillanceNetworks/PrivacyThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/SurveillanceNetworks/PrivacyThreshold.lean#L207

-- Thm stub generated from Applications/SurveillanceNetworks/PrivacyThreshold.lean
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

theorem SurveillanceNetworks.Privacy.card_le_rate_mul_ball(obs : S → M) (dec : M → S) (d : S → S → ℕ) (D B : ℕ)
    (hball : ∀ c : S, (univ.filter fun s => d c s ≤ D).card ≤ B)
    (hrec : ∀ s, d (dec (obs s)) s ≤ D) :
    Fintype.card S ≤ rate obs * B := by sorry
