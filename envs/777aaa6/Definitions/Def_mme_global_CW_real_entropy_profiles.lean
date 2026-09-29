-- Prove2me | Definitions.Def_mme_global_CW_real_entropy_profiles
-- name    : mme_global_CW_real_entropy_profiles
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T08:47:59.198432+00:00
-- url     : https://prove2.me/theorems/6b86f65c-218c-487b-8cdd-cad130239f36
-- title:
--   Real global profiles and the pooled normalized entropy rate
-- statement:
--   Defines real joint and cell-word profiles, their coarse, aggregate and boundary-partition entropy terms, and the three-way pooled rate for arbitrary region weights.
-- source:
--   Finite global entropy and tolerance estimates for More Asymmetry Theorem 5.3.

import Definitions.Def_mme_global_CW_entropy_data
open BigOperators MME MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
namespace MME.GlobalCW

/-- Normalized joint counts and joint cell/word counts; normalization hypotheses
are supplied by theorems, allowing continuity on the surrounding real space. -/
abbrev EntropyProfile (degree R : ℕ) (bounds : Fin R → Fin 3 → ℕ) (W : Type*) :=
  (∀ r, RecursiveThinSplit.Split degree (bounds r) → ℝ) ×
    (Fin 3 → Cell degree R bounds → W → ℝ)

noncomputable def EntropyProfile.coarse {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} (p : EntropyProfile degree R bounds W) (i : Fin 3) (r : Fin R) : ℝ :=
  massEntropy (fun j : Fin (degree+1) ↦
    mme_modern_marginal (fun c ↦ c.val i) (p.1 r) j)

noncomputable def EntropyProfile.words {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (p : EntropyProfile degree R bounds W) (i : Fin 3) (r : Fin R) : ℝ :=
  ∑ j : Fin (degree+1), massEntropy (fun w ↦
    ∑ c : RecursiveThinSplit.Split degree (bounds r), if c.val i = j then p.2 i ⟨r,c⟩ w else 0)

noncomputable def EntropyProfile.compat {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (p : EntropyProfile degree R bounds W) (i : Fin 2) (r : Fin R) : ℝ :=
  (∑ c : {c : RecursiveThinSplit.Split degree (bounds r) // yzBoundary i ⟨r,c⟩},
    massEntropy (fun w ↦ p.2 (yzMode i) ⟨r,c.val⟩ w)) +
  ∑ j : Fin (degree+1), massEntropy (fun w ↦
    ∑ c : RecursiveThinSplit.Split degree (bounds r),
      if ¬ yzBoundary i ⟨r,c⟩ ∧ c.val (yzMode i) = j then p.2 (yzMode i) ⟨r,c⟩ w else 0)

/-- The pooled normalized global rate, with arbitrary nonnegative region weights. -/
noncomputable def EntropyProfile.rate {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (p : EntropyProfile degree R bounds W) (weights : Fin R → ℝ) : ℝ :=
  min (∑ r, weights r * (p.coarse 0 r - Real.log 2 * RecursiveThinSplit.entropyPenalty (p.1 r)))
    (min (∑ r, weights r * (p.coarse 1 r + p.words 1 r - p.compat 0 r))
      (∑ r, weights r * (p.coarse 2 r + p.words 2 r - p.compat 1 r)))
end MME.GlobalCW


