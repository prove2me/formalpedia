-- Prove2me | solution 1 for AlmostLossless.card_silentSlice_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:39.237357+00:00
-- url     : https://prove2.me/submissions/3a4b95cd-e5e6-462d-8b50-d88aa16236aa

-- Sol generated from Geometry/AlmostLosslessChecksum.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessChecksum
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_collisionEvent_mul
/-
# Closing the silent-corruption loophole: a random checksum layer

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`Geometry.AlmostLosslessDecoder` proves that the scanning decoder never returns a
wrong string *provided the transmitted string is typical*.  Adversarial review
exposes the remaining loophole: an **atypical** source string `x ∉ S` can be
silently decoded to some typical `y ≠ x`, because the decoder has no way of
knowing that `x` was atypical.

Here we close that loophole with an independent random checksum
`C : α → Fin K` appended to the codeword (`log₂ K` extra bits).  The key point is
a *conditional independence* (fibrewise counting) argument: for a fixed hash
codebook `H` the candidate returned by the hash decoder is already determined,
so the checksum has only one chance in `K` of confirming it.

* `AlmostLossless.decodeChk_cost` — exact cost `|L| + 1` comparisons.
* `AlmostLossless.decodeChk_never_wrong` — typical strings are still never
  silently corrupted (deterministically).
* `AlmostLossless.silent_corruption_prob_le` — **for every source string, typical
  or not**, the probability of a silent corruption is at most `1 / K`.
-/

open AlmostLossless

open Finset

variable {α : Type*} [DecidableEq α] {M K : ℕ}

/-! ## 1. The checksummed scheme -/




omit [DecidableEq α] in
/-- The checksummed decoder can only output what the hash decoder proposed. -/
theorem decodeChk_output {L : List α} {H : α → Fin M} {C : α → Fin K}
    {p : Fin M × Fin K} {y : α} (h : (decodeChk L H C p).1 = some y) :
    (decode L H p.1).1 = some y := by
  simp only [decodeChk, Option.bind_eq_some_iff] at h
  obtain ⟨z, hz, hzy⟩ := h
  by_cases hc : C z = p.2
  · rw [if_pos hc] at hzy
    rw [hz, hzy]
  · rw [if_neg hc] at hzy
    exact absurd hzy (by simp)


/-! ## 2. The silent-corruption probability, uniformly over all sources -/

variable [Fintype α]









open AlmostLossless in
theorem solution(L : List α) (x : α) (H : α → Fin M) :
    K * (silentSlice L x H K).card ≤ K ^ Fintype.card α := by
  classical
  rcases hd : (decode L H (H x)).1 with _ | y₀
  · -- the hash decoder already refuses: no output at all
    have hempty : silentSlice L x H K = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro C hC
      simp only [silentSlice, mem_filter, mem_univ, true_and, IsSilent] at hC
      obtain ⟨hsome, -⟩ := hC
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
      have := decodeChk_output hy
      rw [show (encChk H C x).1 = H x from rfl, hd] at this
      exact absurd this (by simp)
    rw [hempty]
    simp
  · by_cases hy₀ : y₀ = x
    · -- the hash decoder proposes the correct string: nothing silent can happen
      have hempty : silentSlice L x H K = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro C hC
        simp only [silentSlice, mem_filter, mem_univ, true_and, IsSilent] at hC
        obtain ⟨hsome, hne⟩ := hC
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
        have hout := decodeChk_output hy
        rw [show (encChk H C x).1 = H x from rfl, hd] at hout
        have : y = x := by rw [← hy₀]; exact (Option.some_injective _ hout).symm
        rw [hy, this] at hne
        exact hne rfl
      rw [hempty]
      simp
    · -- the hash decoder proposes a wrong candidate `y₀`: the checksum must collide
      have hsub : silentSlice L x H K ⊆ collisionEvent K y₀ x := by
        intro C hC
        simp only [silentSlice, mem_filter, mem_univ, true_and, IsSilent] at hC
        obtain ⟨hsome, -⟩ := hC
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
        have hout := decodeChk_output hy
        rw [show (encChk H C x).1 = H x from rfl, hd] at hout
        have hyy : y₀ = y := Option.some_injective _ hout
        -- the checksum of the accepted candidate equals the received checksum `C x`
        have hchk : C y = (encChk H C x).2 := by
          simp only [decodeChk, Option.bind_eq_some_iff] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          by_cases hc : C z = (encChk H C x).2
          · rw [if_pos hc] at hzy
            have : z = y := by simpa using hzy
            rw [← this]; exact hc
          · rw [if_neg hc] at hzy
            exact absurd hzy (by simp)
        simp only [collisionEvent, mem_filter, mem_univ, true_and]
        rw [hyy]
        exact hchk
      calc K * (silentSlice L x H K).card
          ≤ K * (collisionEvent K y₀ x).card := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
        _ = K ^ Fintype.card α := card_collisionEvent_mul hy₀
