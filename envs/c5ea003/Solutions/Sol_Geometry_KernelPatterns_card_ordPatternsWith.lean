-- Prove2me | solution 1 for Geometry.KernelPatterns.card_ordPatternsWith
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:34.010444+00:00
-- url     : https://prove2.me/submissions/72ffc66e-3055-4510-a282-ef8435a9fa1e

-- Sol generated from Geometry/KernelPatterns/Fubini.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Faces
import Definitions.Def_Geometry_KernelPatterns_Fubini
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Theorems.Thm_Geometry_KernelPatterns_card_fibre_ordPatterns
import Theorems.Thm_Geometry_KernelPatterns_card_patternsWith_eq_stirlingSecond
import Theorems.Thm_Geometry_KernelPatterns_mem_patternsWith

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


@[simp] lemma mem_reps {v : Fin n → X} {j : Fin n} : j ∈ reps v ↔ pat v j = j := by
  simp [reps]

/-- The representatives biject with the distinct values. -/
theorem card_reps (v : Fin n → X) : (reps v).card = (univ.image v).card := by
  refine Finset.card_bij (fun j _ => v j) (fun a _ => Finset.mem_image_of_mem _ (mem_univ a))
    ?_ ?_
  · intro a ha b hb hab
    rw [mem_reps] at ha hb
    rw [← ha, ← hb]
    exact pat_eq_iff.2 hab
  · intro b hb
    simp only [Finset.mem_image, mem_univ, true_and] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨pat v i, by rw [mem_reps]; exact pat_apply_pat v i, apply_pat v i⟩

@[simp] lemma reps_pat (v : Fin n → X) : reps (pat v) = reps v := by
  ext j; simp

lemma card_image_pat (v : Fin n → X) :
    (univ.image (pat v)).card = (univ.image v).card := by
  rw [← card_reps, ← card_reps, reps_pat]

/-! ### Rank versus the number of blocks -/




/-! ### The fibres of `pat` on ordered patterns -/


/-! ### The Fubini formula -/






/-! ### Faces versus chambers and flats -/




open Geometry.KernelPatterns in
theorem solution(n k : ℕ) :
    (ordPatternsWith n k).card = Nat.stirlingSecond n k * k.factorial := by
  classical
  have hmaps : Set.MapsTo pat ((ordPatternsWith n k : Finset (Fin n → Fin n)) : Set (Fin n → Fin n))
      ((patternsWith n k : Finset (Fin n → Fin n)) : Set (Fin n → Fin n)) := by
    intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq, ordPatternsWith] at hr
    simp only [Finset.mem_coe, mem_patternsWith]
    exact ⟨pat_idem r, by rw [card_image_pat]; exact hr.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfil : ∀ p ∈ patternsWith n k,
      ((ordPatternsWith n k).filter fun r => pat r = p).card = k.factorial := by
    intro p hp
    rw [mem_patternsWith] at hp
    have hset : ((ordPatternsWith n k).filter fun r => pat r = p)
        = ((ordPatterns n).filter fun r => pat r = p) := by
      ext r
      simp only [ordPatternsWith, mem_filter, and_assoc]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨h1, ?_, h3⟩
        rw [← card_image_pat r, h3]
        exact hp.2
    rw [hset]
    exact card_fibre_ordPatterns hp.1 hp.2
  rw [Finset.sum_congr rfl hfil, Finset.sum_const, smul_eq_mul,
    card_patternsWith_eq_stirlingSecond]
