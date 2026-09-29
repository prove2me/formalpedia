-- Prove2me | solution 1 for mme_released_global_profile_normalization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:29:17.319383+00:00
-- url     : https://prove2.me/submissions/070ec1a6-a993-408a-bb91-e11909b829db

import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_released_global_profile_count_identities
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.RecursiveYZ
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

attribute [local irreducible] jointRows alpha atom rowCounts jointCounts coarseCounts wordCounts shapeEquiv

theorem solution (owner : Fin 6) :
    (∀ r c, 0 ≤ (profile owner).1 r c) ∧
    (∀ r, ∑ c, (profile owner).1 r c = 1) ∧
    (∀ i c w, 0 ≤ (profile owner).2 i c w) ∧
    (∀ i c, ∑ w, (profile owner).2 i c w = (profile owner).1 c.1 c.2) ∧
    (∀ (k : ℕ) (r : Fin 1) (c : Shape),
      (counts owner k r c : ℝ) = (blocks k : ℝ)*(profile owner).1 r c) ∧
    (∀ (k : ℕ) (i : Fin 3) (c : Cell 8 1 (fun _ _ ↦ 8)) (w : Word),
      (scaledWords owner k i c w : ℝ) = (blocks k : ℝ)*(profile owner).2 i c w) := by
  have hv := mme_released_global_profile_count_identities owner
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro r c
    unfold profile
    positivity
  · intro r
    change (∑ c, (coarseCounts owner c : ℝ)/(denominator : ℝ)^5) = 1
    rw [← Finset.sum_div,← Nat.cast_sum,hv.1]
    norm_num [denominator]
  · intro i c w
    unfold profile
    positivity
  · intro i c
    change (∑ w, (wordCounts owner i c.2 w : ℝ)/(denominator : ℝ)^5) =
      (coarseCounts owner c.2 : ℝ)/(denominator : ℝ)^5
    rw [← Finset.sum_div,← Nat.cast_sum,hv.2.2.2 i c.2]
  · intro k r c
    unfold counts blocks profile
    push_cast
    norm_num [denominator]
    ring
  · intro k i c w
    unfold scaledWords blocks profile
    push_cast
    norm_num [denominator]
    ring
