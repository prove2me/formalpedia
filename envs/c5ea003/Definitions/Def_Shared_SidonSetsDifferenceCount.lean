-- Prove2me | Definitions.Def_Shared_SidonSetsDifferenceCount
-- name    : Shared_SidonSetsDifferenceCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:14:29.59897+00:00
-- url     : https://prove2.me/theorems/b3913aaa-2383-4faa-8c67-be34616ca63e
-- title:
--   Aether Catalog definitions — Shared_SidonSetsDifferenceCount
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.SidonSetsDifferenceCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/SidonSetsDifferenceCount.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_SidonSetsRigidity

/-!
# Sidon sets V: exact difference counts, and a concrete perfect difference set

Fifth cycle.  Cycle 2 proved that a Sidon set attains the bound `|A|(|A|-1) ≤ |G|-1`
exactly when it is a *perfect difference set*.  A critic's objection to that theorem is
that it might be vacuous — perhaps no perfect difference set exists at all, in which case
the rigidity statement would be an elegant description of the empty set.  This cycle
answers the objection and extracts the arithmetic constraint that perfection imposes.

## Main results

* `IsSidon.card_sub_self` — **exact difference count**: a nonempty Sidon set has exactly
  `|A|² - |A| + 1` differences, the largest conceivable value.  (Contrast with the
  sumset count `|A + A| = C(|A|+1, 2)` of cycle 2: differences are ordered, sums are not.)
* `IsSidon.card_group_of_perfect` — **the order constraint**: a group carrying a perfect
  difference set of size `k` has order exactly `k² - k + 1`.  This is the elementary half
  of the classical restriction; Bruck–Ryser–Chowla and the prime-power conjecture begin
  only afterwards.
* `planarDiffSet13_perfect`, `planarDiffSet13_unique_diff` — **non-vacuity**:
  `{0, 1, 3, 9} ⊆ ℤ/13ℤ` is a perfect difference set, and every nonzero residue mod `13`
  has a *unique* representation as a difference of two of its elements.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): (U1) Sidon-ness should give the difference set its maximum
  possible size `k² - k + 1`, mirroring the sumset identity `|A + A| = C(k+1, 2)`.
  (U2) Perfection is arithmetically rigid: it should pin down `|G|` completely.
  (U3) Perfect difference sets exist, so the rigidity theorem of cycle 2 has content.
Experiment (Experimenter): (U1) was proved by identifying `A - A` with
  `insert 0 (diffSet A)` — the only difference not counted by `diffSet` is `0`, which is
  present precisely because `A` is nonempty.  (U2) followed from `IsSidon.perfect_iff`
  and truncated-subtraction bookkeeping, once `#A * #A` was generalised to an opaque
  variable so `omega` could finish.  (U3) was settled by the explicit witness
  `{0, 1, 3, 9} ⊆ ℤ/13ℤ`: `4 · 4 - 4 = 12 = 13 - 1`, so `perfect_iff` upgrades a finite
  check of the Sidon property into the full statement that all twelve nonzero residues
  are hit exactly once.
Analysis (Analyst): the counting identities of cycles 2 and 5 are dual — sums are
  unordered and give `C(k+1,2)`, differences are ordered and give `k² - k + 1` — and the
  order constraint `|G| = k² - k + 1` is exactly the statement that the difference count
  saturates the group.  The witness `{0, 1, 3, 9}` is the point set of a line in the
  Fano-like plane `PG(2,3)` transported by a Singer cycle, which is why `13 = 3² + 3 + 1`.
Critique (Critic): the finite check `planarDiffSet13_isSidon` is discharged by `decide`,
  but it is *not* the theorem: the mathematical content of `planarDiffSet13_perfect` is
  supplied by `IsSidon.perfect_iff`, a genuine rigidity result, and the same `decide`
  would not by itself prove that every nonzero residue is hit.  `IsSidon.card_sub_self`
  requires `A` nonempty — for `A = ∅` the identity would read `0 = 1` — and the hypothesis
  is load-bearing.
Synthesis (PI): differences saturate at `k² - k + 1`; perfection forces the group order
  to equal that number; and order `13` with `k = 4` realises it, so nothing here is empty.
-/

open Finset Pointwise


section DiffCount
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}




end DiffCount

section PerfectOrder
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A : Finset G}


end PerfectOrder

/-! ## A concrete perfect difference set -/

/-- The classical planar difference set of order `3`: `{0, 1, 3, 9} ⊆ ℤ/13ℤ`. -/
def planarDiffSet13 : Finset (ZMod 13) := {0, 1, 3, 9}


