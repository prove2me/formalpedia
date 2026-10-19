-- Prove2me | Definitions.Def_AT260939824_SupportWitness
-- name    : AT260939824_SupportWitness
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:24:02.208046+00:00
-- url     : https://prove2.me/theorems/4ba8e4ae-9f2d-4400-b7f5-4b3483bd4c89
-- title:
--   Support torsion witnesses and their transport by graph homomorphisms
-- statement:
--   For a finite graph $H$, support torsion data consist of a point $p$ in its support complex, paths $a:p\to\tau p$ and $b:\tau p\to p$, and a natural exponent $k>0$ such that
--   $$b(t)=\tau(a(t))\quad(t\in I),\qquad(a*b)^k\simeq\operatorname{const}_p$$
--   relative to endpoints. A graph homomorphism $f:H\to J$ pushes probability masses forward, hence maps support pairs, paths, and their nullhomotopies into the support complex of $J$. This preserves the same exponent and the swapped-path identity. The selected loop-power compatibility makes that transport an actual witness constructor.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SupportWitness.lean, selected declaration lines 21-30, 48-55, 57-82; SHA-256 e9e09b97cd0dfde8b36ee2a591e1348e436b593b7ceb7722de1e022cd0a88601. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportTorsion
import Definitions.Def_AT260939824_TopologicalWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-!
# Support-space data from an arbitrary odd torsion target

This file removes the intermediate total-neighbor-choice hypothesis.
Every finite graph satisfying the actual odd torsion condition supplies
the two swapped paths and a nullhomotopy of their alternating power.
-/

namespace AbelianTargets

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

/-- The concrete geometric data needed to map the two generator edges and
fill the relation cells of the parity cover. -/
structure SupportTorsionData where
  base : SupportPair H
  a : Path base (SupportPair.swap H base)
  b : Path (SupportPair.swap H base) base
  b_swap : ∀ t, b t = SupportPair.swap H (a t)
  power : ℕ
  power_pos : 0 < power
  null_power : (pathLoopPower (a.trans b) power).Homotopic (Path.refl base)

namespace SupportTorsionData

variable {H}





variable {W : Type*} [Fintype W] {J : SimpleGraph W}

 theorem map_loopPower {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X} (P : Path p p) {f : X → Y} (hf : Continuous f) (n : ℕ) :
    (pathLoopPower P n).map hf = pathLoopPower (P.map hf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (P.trans (pathLoopPower P n)).map hf = (P.map hf).trans (pathLoopPower (P.map hf) n)
    rw [Path.map_trans, ih]

/-- Graph homomorphisms preserve the actual path and nullhomotopy data. -/
def map (f : H →g J) (D : SupportTorsionData H) : SupportTorsionData J := by
  let p := SupportPair.map f D.base
  let a : Path p (SupportPair.swap J p) :=
    (D.a.map (SupportPair.continuous_map f)).cast rfl (SupportPair.map_swap f D.base).symm
  let b : Path (SupportPair.swap J p) p :=
    (D.b.map (SupportPair.continuous_map f)).cast (SupportPair.map_swap f D.base).symm rfl
  have hab : ∀ t, b t = SupportPair.swap J (a t) := by
    intro t
    change SupportPair.map f (D.b t) = SupportPair.swap J (SupportPair.map f (D.a t))
    rw [D.b_swap, SupportPair.map_swap]
  have hloop : (D.a.trans D.b).map (SupportPair.continuous_map f) = a.trans b := by
    apply Path.ext
    funext t
    simp only [Path.map_trans, Path.trans_apply]
    split_ifs <;> rfl
  refine {
    base := p
    a := a
    b := b
    b_swap := hab
    power := D.power
    power_pos := D.power_pos
    null_power := ?_ }
  have hnull := D.null_power.map (SupportPair.continuousMap f)
  simpa only [map_loopPower, hloop] using hnull

end SupportTorsionData





end

end AbelianTargets


