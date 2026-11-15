-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:53:41.239691+00:00
-- url     : https://prove2.me/theorems/7756a7b4-05dc-4070-99f5-3a935aa37fc4
-- title:
--   Explicit rankwise counting envelopes and reverse-doubling horizons
-- statement:
--   The rankwise density floor at rank $d$ is the minimum of the density parameters from rank zero through $d$, computed recursively without choosing an attaining index.
--
--   Given a lower-order error row, the next row starts at zero. At each additional edge it takes the maximum of the preceding-order error at that edge count and the previous next-row value plus the prescribed counting increment. Iterating this row construction from the zero rank gives the rankwise envelope error.
--
--   For a rank bound and edge-count bound, the reverse-doubling horizon is $(\text{edge bound}+1)2^{\text{rank bound}-d}$, using natural subtraction in the exponent. It ensures that the doubled edge-count calls at one lower rank fit the corresponding earlier horizon in the subsequent estimates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/RankwiseBundleEnvelopeSelection.lean#L24-L525

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Lean
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

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## Prefix density floors -/

/-- The least density encountered through rank `d`, written recursively so
that no finite-set choice is involved. -/
def bundleRankwiseDensityFloor (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => α 0
  | d + 1 => min (bundleRankwiseDensityFloor α d) (α (d + 1))











/-! ## The rankwise recurrence -/

/-- The rank-`d + 1` contribution from adjoining the `(n + 1)`st edge. -/
noncomputable def bundleRankwiseStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (lower : ℕ → ℝ) (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

/-- Construct the next error row.  The first branch of the maximum preserves
the preceding-order estimate, while the second absorbs the new counting
increment exactly. -/
noncomputable def bundleRankwiseNextRow
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (d : ℕ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n)

/-- The rankwise bundle-counting envelope. -/
noncomputable def bundleRankwiseEnvelopeError
    (α β μ : ℕ → ℝ) (τ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d)









/-! ## Positivity and monotonicity -/















/-! ## The generalized-counting interface -/



/-! ## Vanishing and continuous rankwise parameter paths -/









/-! ## Density-scaled finite-horizon selection -/



















/-! ## Explicit finite-horizon sufficient bounds -/

/-- Reverse-doubling edge horizon: lower-order calls made while controlling
rank `d + 1` through its horizon fit into the rank-`d` horizon. -/
def bundleReverseDoublingHorizon
    (rankBound edgeBound d : ℕ) : ℕ :=
  (edgeBound + 1) * 2 ^ (rankBound - d)













end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.bundleRankwiseDensityFloor.match_1,
    `Wikipedia.SzemeredisTheorem.bundleRankwiseStepIncrement.eq_1,
    `Wikipedia.SzemeredisTheorem.bundleReverseDoublingHorizon.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


