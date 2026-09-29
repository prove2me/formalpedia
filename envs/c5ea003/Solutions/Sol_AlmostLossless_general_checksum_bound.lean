-- Prove2me | solution 1 for AlmostLossless.general_checksum_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:20:10.514852+00:00
-- url     : https://prove2.me/submissions/fdcef61b-caab-434c-81c1-65fcd999c003

-- Sol generated from Geometry/AlmostLosslessMaster.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessChecksum
import Definitions.Def_Geometry_AlmostLosslessMaster
import Theorems.Thm_AlmostLossless_card_silentPairSlice_mul_le
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
theorem solution(propose : Ω → α → Option α) (x : α) :
    K * (silentPairs propose x K).card ≤ Fintype.card Ω * K ^ Fintype.card α := by
  classical
  have hsub : silentPairs propose x K ⊆
      (univ : Finset Ω).biUnion (fun w => {w} ×ˢ silentPairSlice propose x w K) := by
    intro p hp
    simp only [silentPairs, mem_filter, mem_univ, true_and] at hp
    refine mem_biUnion.2 ⟨p.1, mem_univ _, ?_⟩
    rw [mem_product]
    exact ⟨by simp, by simpa [silentPairSlice] using hp⟩
  have hcard : (silentPairs propose x K).card
      ≤ ∑ w : Ω, (silentPairSlice propose x w K).card := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    refine Finset.sum_le_sum (fun w _ => ?_)
    rw [Finset.card_product, Finset.card_singleton, one_mul]
  calc K * (silentPairs propose x K).card
      ≤ K * ∑ w : Ω, (silentPairSlice propose x w K).card := Nat.mul_le_mul_left _ hcard
    _ = ∑ w : Ω, K * (silentPairSlice propose x w K).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _w : Ω, K ^ Fintype.card α :=
        Finset.sum_le_sum (fun w _ => card_silentPairSlice_mul_le propose x w)
    _ = Fintype.card Ω * K ^ Fintype.card α := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
