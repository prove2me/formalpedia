-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseEnvelopeError_monotone_card
-- name    : Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelopeError_monotone_card
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:46:35.416131+00:00
-- url     : https://prove2.me/theorems/6792d515-ee47-4a91-b0e4-ca534ef9a018
-- title:
--   The rankwise envelope increases with the edge count
-- statement:
--   Let $\alpha,\beta,\mu:\mathbb N\to\mathbb R$ with $\alpha(d),\mu(d)\ge0$ at every rank, and let $\tau\ge0$. At each fixed rank $d$, the canonical rankwise envelope error $E_d(n)$ is nondecreasing in the number $n$ of occurrence edges. No sign condition on $\beta$ is required for this monotonicity statement.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean#L185-L201

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

theorem Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelopeError_monotone_card
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) :
    Monotone (bundleRankwiseEnvelopeError α β μ τ d) := by sorry
