-- Prove2me | solution 1 for MarkoffTransfer.MReach.isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:14:41.897297+00:00
-- url     : https://prove2.me/submissions/359b843f-5917-4f8a-911a-ad32433101a3

-- Sol generated from Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean
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

theorem isCoprime_vieta {x z : ℤ} (y : ℤ) (h : IsCoprime x z) : IsCoprime x (3 * x * y - z) := by
  have h1 : IsCoprime x (-z) := h.neg_right
  have h2 : IsCoprime x (-z + x * (3 * y)) := h1.add_mul_left_right (3 * y)
  have h3 : -z + x * (3 * y) = 3 * x * y - z := by ring
  rwa [h3] at h2


/-! ## The linear obstruction -/




open MarkoffTransfer in
theorem solution{x y z : ℤ} (h : MReach x y z) :
    IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z := by
  induction h with
  | root => exact ⟨isCoprime_one_left, isCoprime_one_left, isCoprime_one_left⟩
  | @vieta x y z _ ih =>
      obtain ⟨hxy, hyz, hxz⟩ := ih
      have hmid : IsCoprime y (MarkoffTransfer.vieta x y z) := by
        have h1 := isCoprime_vieta (x := y) (z := z) x hyz
        have heq : 3 * y * x - z = MarkoffTransfer.vieta x y z := by
          unfold MarkoffTransfer.vieta; ring
        rwa [heq] at h1
      have hout : IsCoprime x (MarkoffTransfer.vieta x y z) := by
        have h1 := isCoprime_vieta (x := x) (z := z) y hxz
        have heq : 3 * x * y - z = MarkoffTransfer.vieta x y z := by
          unfold MarkoffTransfer.vieta; ring
        rwa [heq] at h1
      exact ⟨hxy, hmid, hout⟩
  | swap₁₂ _ ih => exact ⟨ih.1.symm, ih.2.2, ih.2.1⟩
  | swap₂₃ _ ih => exact ⟨ih.2.2, ih.2.1.symm, ih.1⟩
