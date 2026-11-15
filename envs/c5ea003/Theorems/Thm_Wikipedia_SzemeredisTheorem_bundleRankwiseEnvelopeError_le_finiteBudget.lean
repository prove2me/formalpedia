-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseEnvelopeError_le_finiteBudget
-- name    : Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelopeError_le_finiteBudget
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:46:34.911288+00:00
-- url     : https://prove2.me/theorems/ecf4a943-7ba0-4b61-8bf2-df05340df2d6
-- title:
--   A finite numerical budget bounds the rankwise envelope error
-- statement:
--   Let $\alpha,\beta,\mu$ be nonnegative real sequences and $\tau,\eta\ge0$. Fix a natural rank bound $R$ and horizon $h$ such that $2h(d+1)\le h(d)$ for $d<R$, $h(d)\le h(0)$ for $d\le R$, and $Rh(0)\eta\le B$. For every $d<R$ and $n<h(d+1)$, assume $\sqrt{\beta(d+1)(1+B)^2}/\alpha(d+1)^{n+1}\le\eta/2$ and $\tau/\mu(d+1)^{n+1}\le\eta/2$. Then for $d\le R$ and $n\le h(d)$, the rankwise envelope error is at most $d\,h(0)\eta$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean#L600-L708

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

theorem Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelopeError_le_finiteBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound : ℕ) (horizon : ℕ → ℕ)
    (hreverse : ∀ d, d < rankBound →
      2 * horizon (d + 1) ≤ horizon d)
    (hzero : ∀ d, d ≤ rankBound → horizon d ≤ horizon 0)
    (hcap :
      (rankBound : ℝ) * (horizon 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    ∀ d, d ≤ rankBound → ∀ n, n ≤ horizon d →
      bundleRankwiseEnvelopeError α β μ τ d n ≤
        (d : ℝ) * (horizon 0 : ℝ) * η := by sorry
