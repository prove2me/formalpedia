-- Prove2me | Definitions.Def_AT260939824_MarkerExistence
-- name    : AT260939824_MarkerExistence
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:43:38.445668+00:00
-- url     : https://prove2.me/theorems/6165bb8f-297d-4215-83c6-f2271351b286
-- title:
--   Separation and countability of the free binary shift
-- statement:
--   For a dimension $d$, the free binary shift is the subspace of $\{0,1\}^{\mathbb Z^d}$ consisting of configurations with no nonzero translation period. This bundle supplies the inherited $T_1$ separation property and a countable base for its topology.
--
--   The topology is induced by the inclusion into the binary configuration space. These two structural facts are used when constructing clopen graph data on the free shift; the bundle itself does not assert a marker-existence theorem.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 2.1, 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/MarkerExistence.lean, selected declaration lines 208-210, 212-214; SHA-256 a33841719ebcd22734eec82b9054f795f4adf6f5975e148780d77f2cd9efb338. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Existence of clopen separated covering orbit markers

This file completes the positive membership of the concrete graph in
Lemma 7.3. A countable clopen independent cover is built from freeness,
zero-dimensionality, and second countability. The greedy clopen maximal
independent set then supplies the required orbit markers.
-/

namespace AbelianTargets

universe u

noncomputable section







variable {d L : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]



variable [ContinuousVAdd (Lattice d) X]





variable [T1Space X]





variable [SecondCountableTopology X]









instance freeShiftT1Space (d : ℕ) : T1Space (FreeShift d) :=
  inferInstanceAs (T1Space {x : ShiftSpace d //
    ∀ g : Lattice d, shift g x = x → g = 0})

instance freeShiftSecondCountableTopology (d : ℕ) : SecondCountableTopology (FreeShift d) :=
  TopologicalSpace.secondCountableTopology_induced (FreeShift d) (ShiftSpace d)
    (fun x : FreeShift d => x.val)



end

end AbelianTargets


