-- Prove2me | solution 1 for Erdos146.independentBinaryPairMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:59:46.836252+00:00
-- url     : https://prove2.me/submissions/22d910b0-a52a-436d-a6cc-57f6c0a6715a

import Definitions.Def_erdos146_core2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Ring.Basic

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem binaryCoinMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (outcome : Bool) :
    0 ≤ binaryCoinMass q outcome := by
  cases outcome <;> simp [binaryCoinMass] <;> linarith

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (left right : Bool) :
    0 ≤ independentBinaryPairMass q left right := by
  exact mul_nonneg
    (binaryCoinMass_nonneg hqzero hqone left)
    (binaryCoinMass_nonneg hqzero hqone right)
