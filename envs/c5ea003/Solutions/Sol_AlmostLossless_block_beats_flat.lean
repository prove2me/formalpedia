-- Prove2me | solution 1 for AlmostLossless.block_beats_flat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:30:51.159118+00:00
-- url     : https://prove2.me/submissions/e37e0fc2-f21e-49f9-9b77-365067d4af23

-- Sol generated from Geometry/AlmostLosslessBlock.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessBlock
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

open AlmostLossless

open Finset

variable {β : Type*} [Fintype β] [DecidableEq β] {b M : ℕ}

/-! ## 1. The blocked scheme -/




/-! ## 2. No silent corruption, blockwise -/



/-! ## 3. Success of the blocked decoder -/



/-! ## 4. Failure probability: a union bound over the blocks -/






/-! ## 5. The complexity separation -/


  


open AlmostLossless in
theorem solution{t : ℕ} (ht : 2 ≤ t) (hb : 3 ≤ b) : b * t < t ^ b := by
  induction b with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 3 with hn | hn
      · -- base case: n + 1 = 3
        interval_cases n
        · omega
        · omega
        · have h : t ^ (2 + 1) = t * t * t := by ring
          have h4 : 4 * t ≤ t * t * t := by nlinarith
          rw [h]; linarith
      · have hprev : n * t < t ^ n := ih (by omega)
        have hpow : t ≤ t ^ n := Nat.le_self_pow (by omega) t
        calc (n + 1) * t = n * t + t := by ring
          _ < t ^ n + t := by omega
          _ ≤ t ^ n + t ^ n := by omega
          _ = 2 * t ^ n := by ring
          _ ≤ t * t ^ n := Nat.mul_le_mul_right _ ht
          _ = t ^ (n + 1) := by ring
