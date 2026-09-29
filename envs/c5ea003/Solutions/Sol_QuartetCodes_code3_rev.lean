-- Prove2me | solution 1 for QuartetCodes.code3_rev
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:05:19.250238+00:00
-- url     : https://prove2.me/submissions/cdf31bd9-572e-4e85-8db3-6a7086186f5c

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
theorem solution{N p q r s : ℕ} (hp : p ≤ N) (hq : q ≤ N) (hr : r ≤ N) (hs : s ≤ N) :
    code3 (N - p) (N - q) (N - r) (N - s) = code3 p q r s := by
  unfold code3
  split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (exfalso; omega)
