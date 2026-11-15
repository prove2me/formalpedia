-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.bundleRankwiseStepIncrement_le_of_lower_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:23:57.915308+00:00
-- url     : https://prove2.me/submissions/b7499f95-6889-4128-bdfe-b4a643b10fbe

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Rankwise numerical envelopes for bundle counting

The generalized bundle-counting recurrence permits the density and
localized-defect parameters to depend on the rank.  This file supplies a
direct numerical envelope for those rankwise parameters.  Its density floor
is the prefix minimum of the rankwise densities, so no global density lower
bound is needed.

The row constructor takes a maximum with the preceding-order row.  This
makes monotonicity in bundle order automatic even when consecutive ranks use
unrelated parameters; its other branch is equality in the one-edge counting
recurrence.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
/-! ## Prefix density floors -/
/-! ## The rankwise recurrence -/
/-! ## Positivity and monotonicity -/
/-! ## The generalized-counting interface -/
/-! ## Vanishing and continuous rankwise parameter paths -/
/-! ## Density-scaled finite-horizon selection -/
/-! ## Explicit finite-horizon sufficient bounds -/

open Wikipedia.SzemeredisTheorem in
/-- If the two lower-row entries are bounded by `B`, the actual one-edge
increment is bounded by the sum of a defect-only and a uniformity-only
majorant.  This is the separation used by the finite-horizon theorem below. -/
theorem solution
    {α β μ : ℕ → ℝ} {τ B η : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (lower : ℕ → ℝ) (d n : ℕ)
    (hlower_nonneg : ∀ m, 0 ≤ lower m)
    (hlower₁ : lower (n + 1) ≤ B)
    (hlower₂ : lower (2 * (n + 1)) ≤ B)
    (hdefect :
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform :
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseStepIncrement α β μ τ lower d n ≤ η := by
  have hlower₁nonneg : 0 ≤ 1 + lower (n + 1) := by
    linarith [hlower_nonneg (n + 1)]
  have hlower₂nonneg : 0 ≤ 1 + lower (2 * (n + 1)) := by
    linarith [hlower_nonneg (2 * (n + 1))]
  have hB₁nonneg : 0 ≤ 1 + B := by
    linarith [hlower_nonneg (n + 1), hlower₁]
  have hproduct :
      (1 + lower (n + 1)) * (1 + lower (2 * (n + 1))) ≤
        (1 + B) * (1 + B) := by
    exact mul_le_mul
      (by linarith)
      (by linarith)
      hlower₂nonneg hB₁nonneg
  have hradicand :
      β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1))) ≤
        β (d + 1) * (1 + B) * (1 + B) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hproduct (hβ (d + 1))
  have hsqrt :
      Real.sqrt
          (β (d + 1) *
            (1 + lower (n + 1)) *
            (1 + lower (2 * (n + 1)))) ≤
        Real.sqrt (β (d + 1) * (1 + B) * (1 + B)) :=
    Real.sqrt_le_sqrt hradicand
  have hnormalized :
      Real.sqrt
            (β (d + 1) *
              (1 + lower (n + 1)) *
              (1 + lower (2 * (n + 1)))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2 :=
    (div_le_div_of_nonneg_right hsqrt
      (pow_nonneg (hα (d + 1)) (n + 1))).trans hdefect
  unfold bundleRankwiseStepIncrement
  linarith
