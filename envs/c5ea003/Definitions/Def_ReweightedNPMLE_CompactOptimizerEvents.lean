-- Prove2me | Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
-- name    : ReweightedNPMLE_CompactOptimizerEvents
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:16:10.322381+00:00
-- url     : https://prove2.me/theorems/d5ab903b-8eda-5886-ba79-c54983a0345e
-- title:
--   The parameterized optimizer graph
-- statement:
--   For a parameter space \(X\), a candidate space \(M\), and an objective \(U:X\times M\to\mathbb R\), define
--   \[
--   \operatorname{OptGraph}(U)
--   =\{(x,\mu):U(x,\nu)\le U(x,\mu)\text{ for every }\nu\in M\}.
--   \]
--   Equivalently, the section at \(x\) consists of all global maximizers of \(U(x,\cdot)\) over \(M\). The definition retains the full optimizer set and does not choose a particular maximizing candidate. It requires no topological assumptions; continuity of the objective and compactness of the candidate space are imposed separately when proving closedness and measurability properties.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/CompactOptimizerEvents.lean#L22-L23

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Measurable parameterized optimizer events

Continuous optimization on a compact law space has a closed optimizer graph.
Compact projection and countable distance thresholds make failure of
uniqueness and strict optimizer inequalities Borel events. These results are
used to integrate conditional conclusions without assuming a measurable
choice of the conditional good sets.
-/

open Set
open scoped Topology

namespace ReweightedNPMLE

def compactOptimizerGraph {X M : Type*} (U : X × M → ℝ) : Set (X × M) :=
  {p | IsMaxOn univ (fun μ ↦ U (p.1, μ)) p.2}













end ReweightedNPMLE


