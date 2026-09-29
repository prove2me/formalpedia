-- Prove2me | solution 1 for AlmostLossless.card_silentPairSlice_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:18:13.350465+00:00
-- url     : https://prove2.me/submissions/8ddc7691-0267-46a6-b1ef-bfec02639249

-- Sol generated from Geometry/AlmostLosslessMaster.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessChecksum
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessMaster
import Theorems.Thm_AlmostLossless_card_collisionEvent_mul
/-
# The master scheme: blocked random hashing + random checksum

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

This file assembles the previous three ingredients into one scheme and proves a
*general* checksum theorem that does not care how the inner decoder works.

* `AlmostLossless.general_checksum_bound` — **universal error-detection
  theorem**: for *any* inner decoder `propose : Ω → α → Option α` whatsoever
  (deterministic, randomised, blocked, list-decoding, …), appending an
  independent random checksum `C : α → Fin K` makes the probability of a silent
  corruption at most `1/K`, uniformly over all source strings.  The proof is a
  fibrewise (conditional-independence) count: once the inner randomness `ω` is
  fixed, the proposed candidate is determined, so the checksum has a single
  chance in `K` of confirming a wrong candidate.

* The composite scheme `AlmostLossless.blockChkDecode` then satisfies, for a
  typical set `T^b` of size `|T|^b`:
  - exact decoding cost `b·|T| + 1` (`blockChkDecode_cost`),
  - deterministic soundness (`blockChkDecode_never_wrong`),
  - success probability `≥ 1 - ε` for `M ≥ b(|T|-1)/ε`
    (`blockChkDecode_success_prob_ge`),
  - silent-corruption probability `≤ 1/K` for *every* source string, typical or
    not (`blockChk_silent_prob_le`).
-/

open AlmostLossless

open Finset

/-! ## 1. A universal error-detection theorem -/


variable {α : Type*} [Fintype α] [DecidableEq α]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {K : ℕ}








/-! ## 2. The composite scheme: blocks + checksum -/

variable {β : Type*} [Fintype β] [DecidableEq β] {b M K : ℕ}













open AlmostLossless in
omit [Fintype Ω] [DecidableEq Ω] in
theorem solution(propose : Ω → α → Option α) (x : α) (w : Ω) :
    K * (silentPairSlice propose x w K).card ≤ K ^ Fintype.card α := by
  classical
  rcases hd : propose w x with _ | y₀
  · have hempty : silentPairSlice propose x w K = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro C hC
      simp only [silentPairSlice, mem_filter, mem_univ, true_and, IsSilent, chkOutput,
        hd] at hC
      exact absurd hC.1 (by simp)
    rw [hempty]; simp
  · by_cases hy₀ : y₀ = x
    · have hempty : silentPairSlice propose x w K = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro C hC
        simp only [silentPairSlice, mem_filter, mem_univ, true_and, IsSilent, chkOutput,
          hd, Option.bind_some, hy₀] at hC
        simp at hC
      rw [hempty]; simp
    · have hsub : silentPairSlice propose x w K ⊆ collisionEvent K y₀ x := by
        intro C hC
        simp only [silentPairSlice, mem_filter, mem_univ, true_and, IsSilent, chkOutput,
          hd, Option.bind_some] at hC
        by_cases hc : C y₀ = C x
        · simp only [collisionEvent, mem_filter, mem_univ, true_and]
          exact hc
        · rw [if_neg hc] at hC
          exact absurd hC.1 (by simp)
      calc K * (silentPairSlice propose x w K).card
          ≤ K * (collisionEvent K y₀ x).card :=
            Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
        _ = K ^ Fintype.card α := card_collisionEvent_mul hy₀
