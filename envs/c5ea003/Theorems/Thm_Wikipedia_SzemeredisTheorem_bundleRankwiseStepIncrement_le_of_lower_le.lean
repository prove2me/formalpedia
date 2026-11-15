-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseStepIncrement_le_of_lower_le
-- name    : Wikipedia.SzemeredisTheorem.bundleRankwiseStepIncrement_le_of_lower_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:46:35.713953+00:00
-- url     : https://prove2.me/theorems/3c95d01b-bd66-4014-a72e-360be7a52824
-- title:
--   Bounding one rankwise increment from a bounded lower row
-- statement:
--   Let $\alpha,\beta$ be nonnegative real rank schedules and let $L:\mathbb N\to\mathbb R$ be nonnegative. Fix $d,n$ with $L(n+1),L(2(n+1))\le B$. If
--
--   $$
--   \frac{\sqrt{\beta(d+1)(1+B)^2}}{\alpha(d+1)^{n+1}}\le\eta/2,
--   \qquad
--   \frac{\tau}{\mu(d+1)^{n+1}}\le\eta/2,
--   $$
--
--   then the defined rankwise step increment using lower row $L$ at $(d,n)$ is at most $\eta$. The remaining real parameters $\mu,\tau,B,\eta$ have no additional sign hypotheses beyond these displayed conditions.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean#L545-L598

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

theorem Wikipedia.SzemeredisTheorem.bundleRankwiseStepIncrement_le_of_lower_le
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
    bundleRankwiseStepIncrement α β μ τ lower d n ≤ η := by sorry
