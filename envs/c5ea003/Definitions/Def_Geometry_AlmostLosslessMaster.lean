-- Prove2me | Definitions.Def_Geometry_AlmostLosslessMaster
-- name    : Geometry_AlmostLosslessMaster
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:46:32.197888+00:00
-- url     : https://prove2.me/theorems/69858b30-15c1-4ea2-9ea2-9347f1a2cbff
-- title:
--   Aether Catalog definitions — Geometry_AlmostLosslessMaster
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AlmostLosslessMaster`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AlmostLosslessMaster.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessChecksum
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

namespace AlmostLossless

open Finset

/-! ## 1. A universal error-detection theorem -/

section General

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {K : ℕ}

/-- Output of an arbitrary inner decoder followed by a checksum test. -/
def chkOutput (o : Option α) (C : α → Fin K) (x : α) : Option α :=
  o.bind (fun y => if C y = C x then some y else none)

/-- The pairs (inner randomness, checksum) that silently corrupt `x`. -/
def silentPairs (propose : Ω → α → Option α) (x : α) (K : ℕ) : Finset (Ω × (α → Fin K)) :=
  univ.filter (fun p => IsSilent (chkOutput (propose p.1 x) p.2 x) x)

/-- The checksum slice above a fixed inner randomness. -/
def silentPairSlice (propose : Ω → α → Option α) (x : α) (w : Ω) (K : ℕ) :
    Finset (α → Fin K) :=
  univ.filter (fun C => IsSilent (chkOutput (propose w x) C x) x)




end General

/-! ## 2. The composite scheme: blocks + checksum -/

variable {β : Type*} [Fintype β] [DecidableEq β] {b M K : ℕ}

/-- Composite encoder: one codeword per block, plus a global checksum. -/
def blockChkEncode (H : Fin b × β → Fin M) (C : (Fin b → β) → Fin K) (x : Fin b → β) :
    (Fin b → Fin M) × Fin K :=
  (blockEncode H x, C x)

/-- Composite decoder: blockwise scanning decode, then the global checksum test. -/
def blockChkDecode (LT : List β) (H : Fin b × β → Fin M) (C : (Fin b → β) → Fin K)
    (p : (Fin b → Fin M) × Fin K) : Option (Fin b → β) × ℕ :=
  ((blockDecode LT H p.1).1.bind (fun z => if C z = p.2 then some z else none),
   (blockDecode LT H p.1).2 + 1)





/-- The set of composite codebooks (hash, checksum) that recover `x`. -/
def blockChkGood (LT : List β) (x : Fin b → β) (M K : ℕ) :
    Finset ((Fin b × β → Fin M) × ((Fin b → β) → Fin K)) :=
  univ.filter (fun p => (blockChkDecode LT p.1 p.2 (blockChkEncode p.1 p.2 x)).1 = some x)





end AlmostLossless


