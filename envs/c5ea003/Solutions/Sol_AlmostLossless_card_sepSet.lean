-- Prove2me | solution 1 for AlmostLossless.card_sepSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:32:38.130933+00:00
-- url     : https://prove2.me/submissions/5677cff9-8588-400d-9202-80ec716519d1

-- Sol generated from Geometry/AlmostLosslessExact.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Definitions.Def_Geometry_AlmostLosslessExact
import Theorems.Thm_AlmostLossless_card_sepSet_insert
/-
# The exact failure probability of random hashing

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`AlmostLosslessDecoder` gives the upper bound `P[failure] ≤ (|S|-1)/M` and
`AlmostLosslessConverse` the Bonferroni lower bound `P[failure] ≥ (|S|-1)/(2M)`.
Here we compute the quantity **exactly**:

`AlmostLossless.card_sepSet` :  `M^k · |{H : H separates x from D}| = (M-1)^k · M^{|α|}`  (`k = |D|`),

whence `AlmostLossless.failure_prob_exact`:

`P[failure at x] = 1 - (1 - 1/M)^{|S|-1}`.

Both previously proved bounds are corollaries of this identity in the regime
they cover, and the measured values of `AlmostLosslessLabNotes` (`3/4`, `5/9`,
`7/16`, `15/64`, `31/256`) are exactly its values at `|S| = 3`.

The proof is an explicit bijection
`{H separating x from D ∪ {a}} × Fin M  ≃  Σ_{H separating x from D} (Fin M \ {H x})`,
given by `(H, v) ↦ ⟨update H a v, H a⟩`, iterated by induction on `D`.
-/

open AlmostLossless

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}








open AlmostLossless in
theorem solution(x : α) (D : Finset α) (hx : x ∉ D) :
    M ^ D.card * (sepSet D x M).card = (M - 1) ^ D.card * M ^ Fintype.card α := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [sepSet, Finset.card_univ]
  | insert a D ha ih =>
      have hax : a ≠ x := by
        intro h
        exact hx (h ▸ mem_insert_self a D)
      have hxD : x ∉ D := fun h => hx (mem_insert_of_mem h)
      have hstep := card_sepSet_insert (M := M) (x := x) ha hax
      have hIH := ih hxD
      calc M ^ (insert a D).card * (sepSet (insert a D) x M).card
          = M ^ D.card * (M * (sepSet (insert a D) x M).card) := by
            rw [Finset.card_insert_of_notMem ha]; ring
        _ = M ^ D.card * ((M - 1) * (sepSet D x M).card) := by rw [hstep]
        _ = (M - 1) * (M ^ D.card * (sepSet D x M).card) := by ring
        _ = (M - 1) * ((M - 1) ^ D.card * M ^ Fintype.card α) := by rw [hIH]
        _ = (M - 1) ^ (insert a D).card * M ^ Fintype.card α := by
            rw [Finset.card_insert_of_notMem ha]; ring
