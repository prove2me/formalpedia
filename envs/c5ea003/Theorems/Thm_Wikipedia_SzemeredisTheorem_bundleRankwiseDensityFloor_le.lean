-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseDensityFloor_le
-- name    : Wikipedia.SzemeredisTheorem.bundleRankwiseDensityFloor_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:46:35.821124+00:00
-- url     : https://prove2.me/theorems/0928b11a-1435-46c4-b351-2b0e8133ee13
-- title:
--   The prefix density floor is below each earlier density
-- statement:
--   For any real sequence $\alpha$ and natural indices $i\le d$, the bundle rankwise density floor at rank $d$ is at most $\alpha(i)$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean#L51-L65

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

theorem Wikipedia.SzemeredisTheorem.bundleRankwiseDensityFloor_le
    (α : ℕ → ℝ) {i d : ℕ} (hid : i ≤ d) :
    bundleRankwiseDensityFloor α d ≤ α i := by sorry
