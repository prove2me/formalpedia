-- Prove2me | Theorems.Thm_AlmostLossless_blockChkDecode_success_prob_ge
-- name    : AlmostLossless.blockChkDecode_success_prob_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:14.940462+00:00
-- url     : https://prove2.me/theorems/c7d70660-0924-40e2-a106-cae233e6e7bc
-- title:
--   Almost-lossless guarantee for the composite scheme: with
-- statement:
--   **Almost-lossless guarantee for the composite scheme**: with
--   `M ≥ b(|T|-1)/ε`, a random codebook pair recovers a fixed typical string with
--   probability at least `1 - ε`, at a decoding cost of exactly `b|T| + 1`.
--
--   ```lean
--   theorem AlmostLossless.blockChkDecode_success_prob_ge{T : Finset β} {LT : List β} {x : Fin b → β}
--       (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T)
--       (hM : 0 < M) (hK : 0 < K) {ε : ℝ} (hε : 0 < ε)
--       (hMe : (b : ℝ) * ((T.card : ℝ) - 1) / ε ≤ M) (hT : 0 < T.card) :
--       1 - ε ≤ ((blockChkGood LT x M K).card : ℝ) /
--         ((M : ℝ) ^ (b * Fintype.card β) * (K : ℝ) ^ Fintype.card (Fin b → β)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessMaster.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessMaster.lean#L214

-- Thm stub generated from Geometry/AlmostLosslessMaster.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessChecksum
import Definitions.Def_Geometry_AlmostLosslessMaster
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

theorem AlmostLossless.blockChkDecode_success_prob_ge{T : Finset β} {LT : List β} {x : Fin b → β}
    (hnd : LT.Nodup) (hmem : ∀ y, y ∈ LT ↔ y ∈ T) (hx : ∀ i, x i ∈ T)
    (hM : 0 < M) (hK : 0 < K) {ε : ℝ} (hε : 0 < ε)
    (hMe : (b : ℝ) * ((T.card : ℝ) - 1) / ε ≤ M) (hT : 0 < T.card) :
    1 - ε ≤ ((blockChkGood LT x M K).card : ℝ) /
      ((M : ℝ) ^ (b * Fintype.card β) * (K : ℝ) ^ Fintype.card (Fin b → β)) := by sorry
