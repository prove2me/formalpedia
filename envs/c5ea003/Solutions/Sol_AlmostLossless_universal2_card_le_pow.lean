-- Prove2me | solution 1 for AlmostLossless.universal2_card_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:31.030984+00:00
-- url     : https://prove2.me/submissions/1b57e17d-2958-4bd1-95cd-7b96f4191d74

-- Sol generated from Bridges/AlmostLosslessKeyBound.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessLinearHash
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression XI: How Much Randomness Does the Encoder Need?

## Bridge: pigeonhole (combinatorics) ↔ universal hashing (algebra)
##         ↔ derandomization (complexity)

Every achievability theorem of this development starts from a 2-universal family
`H : Fin K → α → Fin M` and *derandomizes* it (`exists_good_key`): the encoder
only has to store one key, i.e. `log₂ K` bits of advice.  Conjecture 5 of the
previous cycle asked how small `K` can be.  Here we prove a hard limit, and it
is the pigeonhole principle again — now applied to the **key space** rather than
to the code space:

* `universal2_card_le_pow` — a 2-universal family with `M ≥ 2` and at least one
  key, on a domain of size `n`, satisfies `n ≤ M^K`;
* `universal2_key_lower_bound` — equivalently `K ≥ log_M n`: the number of keys
  must grow at least logarithmically in the source size, so no constant-size
  family of hash functions can be universal on an unbounded source;
* `linHash_key_bound_sharp_order` — the explicit field family of
  `AlmostLosslessLinearHash` has `K = p` keys on a domain of size `p²`, meeting
  the bound `n ≤ M^K` with room to spare while using only `log₂ p` bits of
  advice: **half** the bits of the message it compresses.

The moral for Monte-Carlo compression: randomness cannot be eliminated, but
`log₂ K` bits of it always suffice, and the field construction already achieves
`log₂ K = ½ log₂ n`.

## Impact: key_space_lower_bound, derandomization_limits
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}





variable (p : ℕ) [Fact p.Prime]




open AlmostLossless in
omit [DecidableEq α] in
theorem solution{H : Fin K → α → Fin M} (hU : Universal2 H)
    (hK : 0 < K) (hM : 2 ≤ M) : Fintype.card α ≤ M ^ K := by
  by_contra hcon
  push_neg at hcon
  have hcards : Fintype.card (Fin K → Fin M) < Fintype.card α := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact hcon
  obtain ⟨x, y, hxy, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun x : α => fun k : Fin K => H k x) hcards
  have hall : (Finset.univ.filter (fun k => H k x = H k y)) = Finset.univ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact congrFun hf k
  have hbound := hU x y hxy
  rw [hall, Finset.card_univ, Fintype.card_fin] at hbound
  -- `K · M ≤ K` with `M ≥ 2` forces `K ≤ 0`
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [hbound, hKR, hMR]
