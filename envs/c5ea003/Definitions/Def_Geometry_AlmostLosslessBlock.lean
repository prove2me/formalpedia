-- Prove2me | Definitions.Def_Geometry_AlmostLosslessBlock
-- name    : Geometry_AlmostLosslessBlock
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:42:06.968227+00:00
-- url     : https://prove2.me/theorems/838108d4-2fad-4281-92f5-e7655fee8a02
-- title:
--   Aether Catalog definitions — Geometry_AlmostLosslessBlock
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AlmostLosslessBlock`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AlmostLosslessBlock.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# Beating the decoder-search barrier: the blocked (product) random code

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

The single-hash almost-lossless scheme of `Geometry.AlmostLosslessDecoder` has
optimal rate but its decoder scans the whole typical set: cost `|S|`, which is
*exponential* in the block length.  Here we remove that obstacle.

Split a string into `b` blocks over a block alphabet `β`, each block typical in
`T : Finset β`, so the global typical set is the product `T^b`, of size
`|T|^b`.  Draw one random codebook `H : Fin b × β → Fin M` and hash each block
*separately*.  Then:

* `AlmostLossless.blockDecode_cost` — the decoder costs exactly `b * |T|` hash
  comparisons, **linear** in the number of blocks, versus `|T| ^ b` for the flat
  scheme (`AlmostLossless.block_beats_flat`: `b * |T| < |T| ^ b`).
* `AlmostLossless.blockDecode_never_wrong` — no silent corruption survives the
  product construction: a decoded string is always the transmitted one.
* `AlmostLossless.blockFail_prob_le` / `AlmostLossless.blockDecode_success_prob_ge` —
  the price is only a union-bound factor `b` in the failure probability:
  `P[failure] ≤ b (|T| - 1) / M`.
-/

namespace AlmostLossless

open Finset

variable {β : Type*} [Fintype β] [DecidableEq β] {b M : ℕ}

/-! ## 1. The blocked scheme -/

/-- The blocked encoder: hash each block with its own slice of the codebook. -/
def blockEncode (H : Fin b × β → Fin M) (x : Fin b → β) : Fin b → Fin M :=
  fun i => H (i, x i)

/-- The blocked decoder: run the scanning decoder of `AlmostLosslessDecoder`
independently on each block, and succeed only if *every* block decodes
unambiguously.  The second component is the total number of hash comparisons. -/
def blockDecode (LT : List β) (H : Fin b × β → Fin M) (c : Fin b → Fin M) :
    Option (Fin b → β) × ℕ :=
  (if h : ∀ i : Fin b, ((decode LT (fun y => H (i, y)) (c i)).1).isSome then
      some (fun i => ((decode LT (fun y => H (i, y)) (c i)).1).get (h i))
    else none,
   ∑ i : Fin b, (decode LT (fun y => H (i, y)) (c i)).2)


/-! ## 2. No silent corruption, blockwise -/



/-! ## 3. Success of the blocked decoder -/

/-- The blocked failure event: some block of `x` collides with another typical
block value under the corresponding slice of the codebook. -/
def blockFail (T : Finset β) (x : Fin b → β) (M : ℕ) : Finset (Fin b × β → Fin M) :=
  univ.filter (fun H => ∃ i : Fin b, ∃ y ∈ T.erase (x i), H (i, y) = H (i, x i))


/-! ## 4. Failure probability: a union bound over the blocks -/



/-- The codebooks on which the blocked scheme recovers `x`. -/
def blockGood (LT : List β) (x : Fin b → β) (M : ℕ) : Finset (Fin b × β → Fin M) :=
  univ.filter (fun H => (blockDecode LT H (blockEncode H x)).1 = some x)



/-! ## 5. The complexity separation -/


  

end AlmostLossless


