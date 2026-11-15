-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
-- name    : Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:46:35.906204+00:00
-- url     : https://prove2.me/theorems/b8d80059-cccd-479a-bf5e-a49b486cbd14
-- title:
--   Reverse-doubling budgets produce an envelope with final error below one half
-- statement:
--   Let $0<\alpha(d)\le1$, $\beta(d)\ge0$, and $\tau,\eta\ge0$. For natural bounds $D,M$, put $H_d=(M+1)2^{D-d}$ and $\mu(d)=\min_{i\le d}\alpha(i)$. Assume $DH_0\eta\le1$ and $DH_0\eta<1/2$, and for every $d<D$ and $n<H_{d+1}$ assume
--
--   $$
--   \frac{\sqrt{4\beta(d+1)}}{\alpha(d+1)^{n+1}}\le\eta/2,
--   \qquad
--   \frac{\tau}{\mu(d+1)^{n+1}}\le\eta/2.
--   $$
--
--   Then the canonical rankwise error schedule is a valid bundle-counting envelope for these density floors and errors, and its value at rank $D$ and edge count $M$ is strictly below $1/2$. The exponent in $H_d$ uses natural subtraction.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean#L738-L785

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

theorem Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
    {α β : ℕ → ℝ} {τ η : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ 1)
    (hfinal :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η < 1 / 2)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ /
          (bundleRankwiseDensityFloor α (d + 1)) ^ (n + 1) ≤
        η / 2) :
    IsBundleCountingEnvelope α β
        (bundleRankwiseDensityFloor α) τ
        (bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ) ∧
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound < 1 / 2 := by sorry
