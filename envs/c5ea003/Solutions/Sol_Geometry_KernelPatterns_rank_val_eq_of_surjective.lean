-- Prove2me | solution 1 for Geometry.KernelPatterns.rank_val_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:02:37.340359+00:00
-- url     : https://prove2.me/submissions/6c08f7b4-63fb-4c7f-bc88-4c967dfc6915

-- Sol generated from Geometry/KernelPatterns/Fubini.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Faces
import Definitions.Def_Geometry_KernelPatterns_Fubini
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Theorems.Thm_Geometry_KernelPatterns_rank_val

/-!
# The Fubini (ordered Bell) formula for faces of the braid arrangement

`Faces.lean` introduced the *ordered pattern* `rank v` of a tuple and showed it
is a complete invariant of the face of the braid arrangement spanned by `v`.
This file counts the ordered patterns exactly:

`#(ordPatterns n) = ∑_{k ≤ n} S(n, k) · k!`,

the ordered Bell (Fubini) numbers `1, 1, 3, 13, 75, 541` (OEIS A000670), where
`S(n, k) = Nat.stirlingSecond n k` counts the kernel patterns with `k` blocks
(`Stirling.lean`).  Geometrically: every face of the braid arrangement is
obtained from a flat (a kernel pattern, i.e. a set partition into `k` blocks) by
choosing one of the `k!` linear orders of its blocks.

The proof fibres `ordPatterns n` first over the number of blocks and then over
the underlying kernel pattern, and identifies each fibre with `Equiv.Perm (Fin k)`
by transporting along the order isomorphism `Fin k ≃o` (block representatives).

Main results:
* `card_reps` — the block representatives biject with the distinct values.
* `rank_val_eq_of_surjective` — for a *surjective* `v : Fin n → Fin k` the rank
  function is the tuple itself; this is the rigidity statement that makes the
  fibres rigid.
* `card_fibre_ordPatterns` — the ordered patterns refining a fixed kernel
  pattern with `k` blocks number exactly `k!`.
* `card_ordPatternsWith` — `#{faces with k blocks} = S(n,k) · k!`.
* `card_ordPatterns_eq_sum_stirlingSecond` — the Fubini formula.
-/

open Geometry.KernelPatterns

open Finset

variable {n k : ℕ} {X : Type*} [LinearOrder X]

/-! ### Block representatives -/






/-! ### Rank versus the number of blocks -/




/-! ### The fibres of `pat` on ordered patterns -/


/-! ### The Fubini formula -/






/-! ### Faces versus chambers and flats -/




open Geometry.KernelPatterns in
theorem solution{v : Fin n → Fin k} (hv : Function.Surjective v)
    (i : Fin n) : (rank v i : ℕ) = (v i : ℕ) := by
  rw [rank_val]
  have hb : (univ.filter fun j => pat v j = j ∧ v j < v i).card
      = ((univ : Finset (Fin k)).filter fun y => y < v i).card := by
    refine Finset.card_bij (fun j _ => v j) ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact ha.2
    · intro a ha b hb hab
      simp only [mem_filter, mem_univ, true_and] at ha hb
      rw [← ha.1, ← hb.1]
      exact pat_eq_iff.2 hab
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      obtain ⟨j, rfl⟩ := hv b
      refine ⟨pat v j, ?_, apply_pat v j⟩
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨pat_apply_pat v j, by rw [apply_pat v j]; exact hb⟩
  rw [hb]
  have h2 : ((univ : Finset (Fin k)).filter fun y => y < v i) = Finset.Iio (v i) := by
    ext x; simp
  rw [h2, Fin.card_Iio]
