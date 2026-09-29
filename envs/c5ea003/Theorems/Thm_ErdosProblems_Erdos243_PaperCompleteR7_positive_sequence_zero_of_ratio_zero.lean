-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_positive_sequence_zero_of_ratio_zero
-- name    : ErdosProblems.Erdos243.PaperCompleteR7.positive_sequence_zero_of_ratio_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:32:31.80313+00:00
-- url     : https://prove2.me/theorems/eef72bc1-33a8-4faf-a2b6-106c39fbc3f1
-- title:
--   Lean source theorem: positive_sequence_zero_of_ratio_zero
-- statement:
--   A strictly positive real sequence tends to zero if its successive-term ratio tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR7/ProductDefect.lean#L25-L55
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The original-coordinate bounded-product-defect corollary

Compiled candidates.  This module supplies the analytic error dictionary
rather than assuming bounded centred error.  Finite upper limsup is stated
as eventual boundedness above by a real constant; the finite initial
segment is irrelevant.  Rationality is given by p/q and HasSum.

The proof avoids assuming a pre-existing double-exponential estimate:
P_n/a_n^2 tends to zero by its successive-ratio identity.  This suffices
for the exact two-term error dictionary.
-/


open Filter
open scoped BigOperators

open ErdosProblems.Erdos243.PaperCompleteR7

theorem ErdosProblems.Erdos243.PaperCompleteR7.positive_sequence_zero_of_ratio_zero
    (u : ℕ → ℝ) (hu : ∀ n, 0 < u n)
    (hratio : Tendsto (fun n ↦ u (n + 1) / u n) atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by sorry
