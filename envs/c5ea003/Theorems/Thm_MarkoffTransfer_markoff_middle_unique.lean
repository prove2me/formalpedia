-- Prove2me | Theorems.Thm_MarkoffTransfer_markoff_middle_unique
-- name    : MarkoffTransfer.markoff_middle_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:54:44.208317+00:00
-- url     : https://prove2.me/theorems/7dcec622-7919-4209-97b6-2a7148f70d31
-- title:
--   Rigidity of the middle entry.
-- statement:
--   **Rigidity of the middle entry.**  If `(x, y, z)` and `(x, y', z)` are ordered positive
--   Markoff triples with the same smallest and largest entries, then `y = y'`.
--
--   Proof: `y` and `y'` are roots of `t² - 3xz·t + (x² + z²)`; if they were distinct they would
--   be *the* two roots, hence `y·y' = x² + z² > z²`, contradicting `y, y' ≤ z`.
--
--   ```lean
--   theorem MarkoffTransfer.markoff_middle_unique{x y y' z : ℤ} (h : IsMarkoff x y z) (h' : IsMarkoff x y' z)
--       (hx : 0 < x) (hyz : y ≤ z) (hyz' : y' ≤ z) (hy : 0 < y) : y = y' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean#L34

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

theorem MarkoffTransfer.markoff_middle_unique{x y y' z : ℤ} (h : IsMarkoff x y z) (h' : IsMarkoff x y' z)
    (hx : 0 < x) (hyz : y ≤ z) (hyz' : y' ≤ z) (hy : 0 < y) : y = y' := by sorry
