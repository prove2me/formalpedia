-- Prove2me | solution 1 for QuartetCodes.revPerm_mul_ne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:00:59.700328+00:00
-- url     : https://prove2.me/submissions/6ac3bac3-dfc0-49a0-832f-6c8641a700f2

-- Sol generated from Combinatorics/QuartetCodesRate.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesRate

/-!
# The caterpillar quartet code is at most half of the leaf orders

The quartet signature of a caterpillar is invariant under reversing the leaf order — an unrooted
tree does not remember which end of the caterpillar is first.  Consequently the *code* (the image
of the signature map inside the ternary cube) has at most `n!/2` words, which is the packing
statement complementing the lower-bound construction of `Combinatorics.QuartetCodes`: the trees
one may pick from are the codewords, and there are at most `n!/2` of them, while the ambient
ternary space has `3^(n choose 4)` points.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Reversal is a symmetry of the quartet signature, so the signature map is at least two-to-one; more
symmetries (swapping the first two, resp. last two, leaves) should push the index to `8`, and the
five-leaf computation in `Combinatorics.QuartetCodesConsistency` (`15 = 5!/8`) says the index is
exactly `8`.

## Experiment (Experimenter)
The reversal invariance is proved here for *all* quadruples, degenerate ones included, because the
reversal `v ↦ N - v` flips every comparison at once.  (The other two symmetries genuinely need the
four leaves to be distinct: for the value transposition `0 ↔ 1` the degenerate quadruple
`(0,0,1,5)` changes its type, so those symmetries only act on the non-degenerate part.)

## Analysis (Analyst)
The index-2 bound is what a *global* symmetry gives; the remaining factor `4` comes from the two
local cherry symmetries at the ends of the caterpillar and is visible in the exact five-leaf count.

## Critique (Critic)
The bound is stated for the full signature function (all ordered quadruples), so it is a statement
about a concrete finite code and not about an equivalence class chosen for convenience.
-/

open Finset

open QuartetCodes


variable {n : ℕ}








open QuartetCodes in
theorem solution(hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) :
    (Fin.revPerm * π : Equiv.Perm (Fin n)) ≠ π := by
  intro h
  have h0 : (0 : ℕ) < n := by omega
  set x : Fin n := π.symm ⟨0, h0⟩ with hxdef
  have hx : (Fin.revPerm * π : Equiv.Perm (Fin n)) x = π x := by rw [h]
  rw [Equiv.Perm.mul_apply] at hx
  have hpx : π x = ⟨0, h0⟩ := by rw [hxdef, Equiv.apply_symm_apply]
  rw [hpx] at hx
  have hv : ((Fin.revPerm : Equiv.Perm (Fin n)) ⟨0, h0⟩).val = n - 1 := by
    simp [Fin.revPerm, Fin.val_rev]
  have := congrArg Fin.val hx
  rw [hv] at this
  simp at this
  omega
