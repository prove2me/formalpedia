-- Prove2me | Theorems.Thm_MarkoffTransfer_MReach_isCoprime
-- name    : MarkoffTransfer.MReach.isCoprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:54:00.102317+00:00
-- url     : https://prove2.me/theorems/a6b69274-0f70-42bd-ab8a-4c55c31770da
-- title:
--   Primitivity transfer.
-- statement:
--   **Primitivity transfer.**  Every triple of the Markoff tree is pairwise coprime — the
--   Markoff analogue of the primitivity of Berggren's Pythagorean triples, proved by the same
--   "invariant along the tree" method.
--
--   ```lean
--   theorem MarkoffTransfer.MReach.isCoprime{x y z : ℤ} (h : MReach x y z) :
--       IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean#L91

-- Thm stub generated from Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary
import Definitions.Def_Cryptography_MarkoffTransfer_UniquenessAndNonlinearity

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

open MarkoffTransfer

/-! ## The outer pair determines the middle entry -/



/-! ## Reduction of the Markoff uniqueness conjecture -/




/-! ## Pairwise coprimality along the tree -/

theorem MarkoffTransfer.MReach.isCoprime{x y z : ℤ} (h : MReach x y z) :
    IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z := by sorry
