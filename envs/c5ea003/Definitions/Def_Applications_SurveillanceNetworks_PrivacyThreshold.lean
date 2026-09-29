-- Prove2me | Definitions.Def_Applications_SurveillanceNetworks_PrivacyThreshold
-- name    : Applications_SurveillanceNetworks_PrivacyThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:07.537423+00:00
-- url     : https://prove2.me/theorems/6ab30b36-6cff-4205-ab78-25cfa73d6fa6
-- title:
--   Aether Catalog definitions — Applications_SurveillanceNetworks_PrivacyThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SurveillanceNetworks.PrivacyThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SurveillanceNetworks/PrivacyThreshold.lean by skeleton subtraction
import Mathlib
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

namespace SurveillanceNetworks.Privacy

variable {S M : Type*}

/-! ## Privacy and distortion for deterministic channels -/

/-- A deterministic channel is perfectly private when the record it emits does not
depend on the configuration. -/
def PerfectPrivacy (obs : S → M) : Prop := ∀ s t, obs s = obs t

/-- The distortion budget `D` is *privately achievable* over the record alphabet
`M` if some perfectly private channel and decoder reconstruct every configuration
to within `D`. -/
def PrivatelyAchievable (M : Type*) (d : S → S → ℕ) (D : ℕ) : Prop :=
  ∃ (obs : S → M) (dec : M → S), PerfectPrivacy obs ∧ ∀ s, d (dec (obs s)) s ≤ D


/-! ## Privacy and distortion for randomized channels -/

/-- A randomized channel `ch : S → PMF M` is perfectly private when the law of the
record is the same for every configuration. -/
def RandPerfectPrivacy (ch : S → PMF M) : Prop := ∀ s t, ch s = ch t

/-- The budget `D` is *privately achievable by a randomized channel* if some
perfectly private randomized channel and decoder reconstruct every configuration
to within `D` almost surely (i.e. for every record in the support). -/
def RandPrivatelyAchievable (M : Type*) (d : S → S → ℕ) (D : ℕ) : Prop :=
  ∃ (ch : S → PMF M) (dec : M → S),
    RandPerfectPrivacy ch ∧ ∀ s, ∀ m ∈ (ch s).support, d (dec m) s ≤ D



/-! ## The optimal private distortion is the covering radius -/

/-- The covering radius of the one-codeword code: the smallest radius `r` such
that some single ball of radius `r` covers the configuration space. -/
noncomputable def coveringRadius (d : S → S → ℕ) : ℕ := sInf {r | ∃ c : S, ∀ s, d c s ≤ r}




/-! ## Hamming distortion on binary tensors -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Hamming distance between two binary tensors indexed by `α`. -/
def hdist (x y : α → Bool) : ℕ := (univ.filter fun i => x i ≠ y i).card








/-! ## Exact covering converse -/

variable [Fintype S] [DecidableEq S] [DecidableEq M]

/-- The **rate** of a channel: the number of distinct records it emits. -/
def rate (obs : S → M) : ℕ := (univ.image obs).card






end SurveillanceNetworks.Privacy


