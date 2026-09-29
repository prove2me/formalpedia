-- Prove2me | solution 1 for AlmostLossless.blockChkDecode_success_prob_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:29:24.930067+00:00
-- url     : https://prove2.me/submissions/f242ea49-0bfa-45d3-b937-2db62b0786da

-- Sol generated from Geometry/AlmostLosslessMaster.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessChecksum
import Definitions.Def_Geometry_AlmostLosslessMaster
import Theorems.Thm_AlmostLossless_blockDecode_success_prob_ge
import Theorems.Thm_AlmostLossless_card_codebooks
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








/-- Adding the checksum does not cost any success probability: the good set of the
composite scheme contains a full product slab over the good hash codebooks. -/
theorem card_blockChkGood_ge (LT : List β) (x : Fin b → β) :
    (blockGood LT x M).card * K ^ Fintype.card (Fin b → β)
      ≤ (blockChkGood LT x M K).card := by
  classical
  have hsub2 : (blockGood LT x M) ×ˢ (univ : Finset ((Fin b → β) → Fin K))
      ⊆ blockChkGood LT x M K := by
    intro p hp
    rw [mem_product] at hp
    have hH : (blockDecode LT p.1 (blockEncode p.1 x)).1 = some x := by
      simpa [blockGood] using hp.1
    simp [blockChkGood, blockChkDecode, blockChkEncode, hH]
  have hcard2 := Finset.card_le_card hsub2
  rwa [Finset.card_product, Finset.card_univ, card_codebooks] at hcard2





open AlmostLossless in
theorem solution{T : Finset β} {LT : List β} {x : Fin b → β}
    (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T)
    (hM : 0 < M) (hK : 0 < K) {ε : ℝ} (hε : 0 < ε)
    (hMe : (b : ℝ) * ((T.card : ℝ) - 1) / ε ≤ M) (hT : 0 < T.card) :
    1 - ε ≤ ((blockChkGood LT x M K).card : ℝ) /
      ((M : ℝ) ^ (b * Fintype.card β) * (K : ℝ) ^ Fintype.card (Fin b → β)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hpow : (0 : ℝ) < (M : ℝ) ^ (b * Fintype.card β) := by positivity
  have hpowK : (0 : ℝ) < (K : ℝ) ^ Fintype.card (Fin b → β) := by positivity
  have hbase := blockDecode_success_prob_ge (M := M) hnd hmem hx hM hε hMe hT
  have hprod : ((blockGood LT x M).card : ℝ) * (K : ℝ) ^ Fintype.card (Fin b → β)
      ≤ ((blockChkGood LT x M K).card : ℝ) := by
    have h := card_blockChkGood_ge (M := M) (K := K) LT x
    exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hpow] at hbase
  nlinarith [hbase, hprod, hpowK, hpow]
