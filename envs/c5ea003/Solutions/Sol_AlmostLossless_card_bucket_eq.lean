-- Prove2me | solution 1 for AlmostLossless.card_bucket_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:19:07.155792+00:00
-- url     : https://prove2.me/submissions/8ee9c475-1fb0-4773-9f24-e5fa022b6b20

-- Sol generated from Logic/AlmostLossless/Instances.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme

/-!
# Instances: linear scan, bucketed scan, and a concrete `ZMod p` compressor

Two instances of `AlmostLossless.ScanScheme`:

* `AlmostLossless.linearScan` — the decoder scans the whole typical set:
  cost exactly `|T|` hash evaluations, deterministic worst case.
* `AlmostLossless.bucketed` — the codeword is a pair (bucket hash, checksum
  hash) and the decoder scans only one bucket, taken from a precomputed index
  of `T`.  Its cost when decoding a typical word `x` is exactly
  `1 + collisionCount`, and the *expected* cost over the random seed is at most
  `1 + (|T|-1)/m₁` (`AlmostLossless.avg_decodeCost_bucketed_le`): the decoder
  becomes essentially constant-time once `m₁ ≳ |T|`, while the transmitted rate
  is `log m₁ + log m₂` bits.

Finally `AlmostLossless.zmod_scheme` packages the whole pipeline over
`(ZMod p)^k` with the inner-product hash family: `k` field symbols are
compressed to *one* symbol plus a failure flag, the decoder is honest for every
seed, its cost is exactly `|T|`, and the average failure probability is at most
`ε + |T|(|T|-1)/p`.  The companion statement
`AlmostLossless.zmod_uniform_hopeless` shows this is no contradiction with the
pigeonhole bound: on the *uniform* source the very same alphabet fails with
probability at least `1 - (p+1)/p^k`.
-/

open AlmostLossless

open Finset

variable {S A M : Type*} [DecidableEq S] [DecidableEq M]

/-! ## The linear-scan scheme -/



/-! ## The bucketed scheme -/


variable {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂]






/-! ## A concrete compressor over `(ZMod p)^k` -/


variable {p k : ℕ} [Fact p.Prime]







open AlmostLossless in
theorem solution(T : Finset S) (h₁ : A₁ → S → M₁) (a₁ : A₁) {x : S} (hx : x ∈ T) :
    #{t ∈ T | h₁ a₁ t = h₁ a₁ x} = 1 + collisionCount h₁ T a₁ x := by
  classical
  have hins : ({t ∈ T | h₁ a₁ t = h₁ a₁ x} : Finset S)
      = insert x ({t ∈ T.erase x | h₁ a₁ t = h₁ a₁ x} : Finset S) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hyT, hy⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨⟨hyx, hyT⟩, hy⟩
    · rintro (rfl | ⟨⟨_, hyT⟩, hy⟩)
      · exact ⟨hx, rfl⟩
      · exact ⟨hyT, hy⟩
  have hnot : x ∉ ({t ∈ T.erase x | h₁ a₁ t = h₁ a₁ x} : Finset S) := by
    simp only [Finset.mem_filter, Finset.mem_erase]
    rintro ⟨⟨hne, _⟩, _⟩
    exact hne rfl
  rw [hins, Finset.card_insert_of_notMem hnot, collisionCount, Nat.add_comm]
