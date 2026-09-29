-- Prove2me | Definitions.Def_Combinatorics_QuartetCodesRate
-- name    : Combinatorics_QuartetCodesRate
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:47:26.735827+00:00
-- url     : https://prove2.me/theorems/65c0b5a5-0407-45a5-becb-ba26161dcf42
-- title:
--   Aether Catalog definitions — Combinatorics_QuartetCodesRate
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.QuartetCodesRate`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/QuartetCodesRate.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes

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

namespace QuartetCodes

section Rate

variable {n : ℕ}


/-- The full quartet signature of a leaf order: the ternary word indexed by ordered quadruples of
leaves. -/
def sigAll (π : Equiv.Perm (Fin n)) : Fin n × Fin n × Fin n × Fin n → Fin 3 :=
  fun q => qcode π q.1 q.2.1 q.2.2.1 q.2.2.2




end Rate

end QuartetCodes


