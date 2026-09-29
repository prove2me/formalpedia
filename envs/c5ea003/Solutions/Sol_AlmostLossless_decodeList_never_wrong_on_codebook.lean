-- Prove2me | solution 1 for AlmostLossless.decodeList_never_wrong_on_codebook
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:06:19.085844+00:00
-- url     : https://prove2.me/submissions/e03ce5b9-47ba-44dc-a815-d3d40620be5c

/-
# `AlmostLossless.decodeList_never_wrong_on_codebook`
Target `aa3dc866` (Open; re-read live immediately before submitting).

ORDINARY PROOF — closure screens CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries six):
    ∀ {α : Type} {M : ℕ} {h : α → Fin M} {l : List α} {x y : α},
      x ∈ l → AlmostLossless.decodeList h l (h x) = some y → y = x
**NO instances whatsoever** — no `[Fintype α]`, no `[DecidableEq α]`. That matches its section
exactly: `section Decoder` (line 83) declares only `variable {α : Type*} {M : ℕ}`, unlike the
`Universal` section above it (line 48) which adds both. `decodeList` needs neither: `Fin M` already
has decidable equality, and nothing quantifies over `α`. Six submissions were rejected on type here.

DEFINITIONS (read from the bundle):
    scanCost h i []       = ([], 0)
    scanCost h i (y :: ys) = (if h y = i then y :: (scanCost h i ys).1 else (scanCost h i ys).1,
                              (scanCost h i ys).2 + 1)
    decodeList h l i      = match (scanCost h i l).1 with | [y] => some y | _ => none

MATHS. The decoder answers `some y` ONLY when the scan found a UNIQUE match — that uniqueness is the
whole mechanism preventing silent corruption. So if it answered `some y` while `x` is in the codebook
and `i = h x`, then `x` is itself a match, hence a member of the match list; a singleton list
containing `x` can only be `[x]`; therefore `y = x`.

The one real step is the scan's completeness on its own key:
    x ∈ l → x ∈ (scanCost h (h x) l).1
proved by induction on `l` along `scanCost`'s own recursion — the head case takes the `if` branch
`h x = h x` by `rfl`, the tail case is the hypothesis.
-/
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlmostLossless

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {α : Type*} {M : ℕ} {h : α → Fin M} {l : List α} {x y : α}
    (hx : x ∈ l) (hy : decodeList h l (h x) = some y) : y = x := by
  -- the scan is complete on its own key: a member of the list is a member of the match list
  have hmem : ∀ (m : List α), x ∈ m → x ∈ (scanCost h (h x) m).1 := by
    intro m
    induction m with
    | nil => intro hc; exact absurd hc (List.not_mem_nil)
    | cons z zs ih =>
        intro hc
        rw [scanCost]
        rcases List.mem_cons.mp hc with rfl | htl
        · simp
        · by_cases hz : h z = h x
          · simp only [if_pos hz]
            exact List.mem_cons_of_mem _ (ih htl)
          · simp only [if_neg hz]
            exact ih htl
  have hxin : x ∈ (scanCost h (h x) l).1 := hmem l hx
  -- the decoder answered, so the match list is a singleton; it contains x, so it is [x]
  rw [decodeList] at hy
  cases hs : (scanCost h (h x) l).1 with
  | nil =>
      rw [hs] at hxin
      exact absurd hxin (List.not_mem_nil)
  | cons a as =>
      cases as with
      | nil =>
          rw [hs] at hy hxin
          have hax : a = x := by
            rcases List.mem_cons.mp hxin with hh | htl
            · exact hh.symm
            · exact absurd htl (List.not_mem_nil)
          rw [← Option.some_inj.mp hy, hax]
      | cons b bs =>
          rw [hs] at hy
          simp at hy
