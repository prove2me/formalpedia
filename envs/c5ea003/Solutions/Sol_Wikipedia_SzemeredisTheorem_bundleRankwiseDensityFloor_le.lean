-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.bundleRankwiseDensityFloor_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:23:57.875461+00:00
-- url     : https://prove2.me/submissions/87ec709e-07fb-465f-8a47-fae8c953cb13

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

section


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





@[simp]
theorem bundleRankwiseDensityFloor_succ (α : ℕ → ℝ) (d : ℕ) :
    bundleRankwiseDensityFloor α (d + 1) =
      min (bundleRankwiseDensityFloor α d) (α (d + 1)) :=
  rfl







/-! ## The rankwise recurrence -/















/-! ## Positivity and monotonicity -/















/-! ## The generalized-counting interface -/



/-! ## Vanishing and continuous rankwise parameter paths -/









/-! ## Density-scaled finite-horizon selection -/



















/-! ## Explicit finite-horizon sufficient bounds -/















end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- The prefix floor at `d` lies below every density of rank at most `d`. -/
theorem solution
    (α : ℕ → ℝ) {i d : ℕ} (hid : i ≤ d) :
    bundleRankwiseDensityFloor α d ≤ α i := by
  induction d with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hid
      subst i
      exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      by_cases hi : i = d + 1
      · subst i
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hid hi)))
