-- Prove2me | solution 1 for AlmostLossless.decode_success_of_not_mem_failSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:20:56.812323+00:00
-- url     : https://prove2.me/submissions/69093c69-85ac-486a-b2b8-673f7073d61a

-- Sol generated from Geometry/AlmostLosslessDecoder.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_decode_cost
import Theorems.Thm_AlmostLossless_decode_fst_eq_some_iff
/-
# Almost-lossless compression: an explicit decoder, its cost, and its failure probability

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

The scheme.  Fix a *typical set* `S : Finset α` (the strings the source actually
produces with high probability), enumerated as a duplicate-free candidate list
`L`, and a codebook `H : α → Fin M` drawn uniformly at random.  The encoder sends
`H x` (`⌈log₂ M⌉` bits).  The decoder scans `L`, collects all `y` with
`H y = H x`, and

* outputs `some y` **only** when that list is a singleton, and
* outputs `none` otherwise.

Main results:

* `AlmostLossless.decode_cost` — the decoder performs **exactly `|L|`** hash
  comparisons (an exact complexity figure, not an asymptotic one).
* `AlmostLossless.decode_never_wrong` — *no silent corruption*: whenever the
  decoder outputs a string, that string is the transmitted one.  Errors are
  always reported as `none`.
* `AlmostLossless.decode_success_of_not_mem_failSet` — the decoder succeeds
  unless the codebook collides on the typical set.
* `AlmostLossless.failSet_prob_le` / `AlmostLossless.success_prob_ge` — the
  Shannon random-coding bound in exact counting form and in ℝ:
  `P[failure] ≤ (|S| - 1)/M`, hence `P[success] ≥ 1 - ε` as soon as
  `M ≥ (|S| - 1)/ε`.
* `AlmostLossless.exists_good_codebook` — derandomisation: some *fixed*
  codebook of size `M` fails on at most `|S|(|S|-1)/M` typical strings.
-/

open AlmostLossless

open Finset

/-! ## 1. The scanning decoder and its exact cost -/

variable {α : Type*} [DecidableEq α] {M : ℕ}







/-! ## 2. No silent corruption -/



/-! ## 3. When does the decoder succeed? -/

variable [Fintype α]



/-! ## 4. The random-coding bound -/






/-! ## 5. Derandomisation: a single good codebook exists -/




open AlmostLossless in
theorem solution{S : Finset α} {L : List α} {x : α}
    {H : α → Fin M} (hnd : L.Nodup) (hmem : ∀ y, y ∈ L ↔ y ∈ S)
    (hx : x ∈ S) (hH : H ∉ failSet S x M) :
    decode L H (H x) = (some x, L.length) := by
  have hno : ∀ y ∈ S, y ≠ x → H y ≠ H x := by
    intro y hy hyx hHy
    exact hH (by
      simp only [failSet, mem_filter, mem_univ, true_and]
      exact ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, hHy⟩)
  -- the candidate list is exactly `[x]`
  set F := L.filter (fun z => H z = H x) with hF
  have hnodup : F.Nodup := hnd.filter _
  have hall : ∀ z ∈ F, z = x := by
    intro z hz
    rw [hF, List.mem_filter] at hz
    by_contra hzx
    exact hno z ((hmem z).1 hz.1) hzx (by simpa using hz.2)
  have hxmem : x ∈ F := by
    rw [hF, List.mem_filter]
    exact ⟨(hmem x).2 hx, by simp⟩
  have hsub : F ⊆ [x] := by
    intro z hz; simpa using hall z hz
  have hlen1 : F.length ≤ 1 := by
    have := (hnodup.subperm hsub).length_le
    simpa using this
  have hlen2 : 1 ≤ F.length := List.length_pos_of_mem hxmem
  have hlen : F.length = 1 := le_antisymm hlen1 hlen2
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlen
  have hax : a = x := hall a (by rw [ha]; simp)
  have hFx : F = [x] := by rw [ha, hax]
  have hfst : (decode L H (H x)).1 = some x :=
    (decode_fst_eq_some_iff L H (H x) x).2 (by rw [← hF, hFx])
  exact Prod.ext hfst (decode_cost L H (H x))
