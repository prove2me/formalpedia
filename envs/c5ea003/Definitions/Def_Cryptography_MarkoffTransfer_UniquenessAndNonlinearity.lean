-- Prove2me | Definitions.Def_Cryptography_MarkoffTransfer_UniquenessAndNonlinearity
-- name    : Cryptography_MarkoffTransfer_UniquenessAndNonlinearity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:20:55.568697+00:00
-- url     : https://prove2.me/theorems/ff4c7132-eb87-4f00-97a0-0fbab443b55e
-- title:
--   Aether Catalog definitions — Cryptography_MarkoffTransfer_UniquenessAndNonlinearity
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.MarkoffTransfer.UniquenessAndNonlinearity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary

/-!
# Cycle 2: What the Transfer *Does* Buy on the Markoff Side

Cycle 1 showed that the Berggren ternary tree and the Markoff binary tree are not
isomorphic, and located the two obstructions (ternary vs binary branching; silver vs
golden growth).  This file harvests the parts of the Berggren methodology — descent,
unique parents, and the "one coordinate determines the rest" style of argument — that
*do* apply to the Markoff tree, and pins down the exact reason the Berggren *linear*
(Lorentz) machinery cannot be imported.

## Main results

* `markoff_middle_unique` — **the smallest and largest entries determine the middle one.**
  Two ordered Markoff triples with the same outer pair are equal.
* `markoff_unique_of_min_one` — consequently, for a fixed top entry there is at most one
  ordered Markoff triple with smallest entry `1`.
* `markoff_uniqueness_iff_min_determined` — a **reduction of the (open) Markoff uniqueness
  conjecture**: uniqueness of the whole triple given the maximum is equivalent to
  uniqueness of the *minimum* given the maximum.  The middle entry is free of charge.
* `MReach.isCoprime` — every tree triple is pairwise coprime (transfer of the Berggren
  primitivity invariant, proved by induction along the tree).
* `vieta_not_linear` — **the linear obstruction.**  The Berggren moves act on triples by
  integer matrices preserving the Lorentz form `a² + b² - c²`
  (`BerggrenSpectral.berg_isometry_*`).  No matrix whatsoever implements the Markoff Vieta
  move on the Markoff surface: the move is genuinely quadratic.  This is the structural
  reason the Lorentz/hyperbolic half of the Berggren machinery cannot be transported.
-/

namespace MarkoffTransfer

/-! ## The outer pair determines the middle entry -/



/-! ## Reduction of the Markoff uniqueness conjecture -/

/-- The Markoff uniqueness conjecture (open): an ordered positive Markoff triple is
determined by its largest entry. -/
def MarkoffUniqueness : Prop :=
  ∀ x y x' y' z : ℤ, 0 < x → x ≤ y → y ≤ z → IsMarkoff x y z →
    0 < x' → x' ≤ y' → y' ≤ z → IsMarkoff x' y' z → x = x' ∧ y = y'

/-- The weaker statement that only the *smallest* entry is determined by the largest. -/
def MarkoffMinUniqueness : Prop :=
  ∀ x y x' y' z : ℤ, 0 < x → x ≤ y → y ≤ z → IsMarkoff x y z →
    0 < x' → x' ≤ y' → y' ≤ z → IsMarkoff x' y' z → x = x'


/-! ## Pairwise coprimality along the tree -/



/-! ## The linear obstruction -/



end MarkoffTransfer


