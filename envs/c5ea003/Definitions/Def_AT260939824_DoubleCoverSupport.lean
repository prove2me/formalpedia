-- Prove2me | Definitions.Def_AT260939824_DoubleCoverSupport
-- name    : AT260939824_DoubleCoverSupport
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:21:42.513489+00:00
-- url     : https://prove2.me/theorems/798407ff-e25f-4109-8693-ea274eca9e02
-- title:
--   Support realization of the bipartite double cover
-- statement:
--   Given a graph $H$ and a chosen adjacent neighbor at each vertex, the two copies of each vertex are represented by points in the support-pair space. Oriented edges are assigned paths and homotopy classes between these points. Reversing an edge reverses its class, and closed four-walks have trivial class. These certificates package an actual realization compatible with the defining reduced-walk relations.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/DoubleCoverSupport.lean, selected declaration lines 20-23, 25-30, 32-36, 57-63, 65-70, 72-89, 91-139, 141-147; SHA-256 2fca52e6371811b5905e2c27e18a049c2d11b2745429f7764c435715a4a4ee35. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
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
# Realization of the graph double cover in the support complex

The chosen-neighbor edge routes of Lemma 6.2 respect spur and four-walk
cancellation.  This file constructs that realization and proves its
compatibility with the reduced graph-walk homotopy presentation.
-/

namespace AbelianTargets

noncomputable section

variable {V : Type*} [Fintype V] (H : SimpleGraph V)
  (s : V → V) (hs : ∀ v, H.Adj v (s v))

/-- The two lifts of a vertex are exchanged by the support-shore swap. -/
def doublePoint : V ⊕ V → SupportPair H
  | .inl v => SupportPair.vertex H (hs v)
  | .inr v => SupportPair.vertex H (hs v).symm

def doubleEdgeClass : EdgeClasses H.bipartiteDoubleCover (doublePoint H s hs)
  | .inl u, .inr v, h => SupportPair.doubleClass H (hs u) h (hs v).symm
  | .inr u, .inl v, h => Path.Homotopic.Quotient.symm
      (SupportPair.doubleClass H (hs v) h.symm (hs u).symm)
  | .inl _, .inl _, h => h.elim
  | .inr _, .inr _, h => h.elim

def doubleEdgePath : EdgePaths H.bipartiteDoubleCover (doublePoint H s hs)
  | .inl u, .inr v, h => SupportPair.doubleEdgePath H (hs u) h (hs v).symm
  | .inr u, .inl v, h => (SupportPair.doubleEdgePath H (hs v) h.symm (hs u).symm).symm
  | .inl _, .inl _, h => h.elim
  | .inr _, .inr _, h => h.elim





theorem doubleEdgeClass_reverse {a b : V ⊕ V} (h : H.bipartiteDoubleCover.Adj a b) :
    doubleEdgeClass H s hs h.symm = Path.Homotopic.Quotient.symm (doubleEdgeClass H s hs h) := by
  cases a <;> cases b
  · exact h.elim
  · rfl
  · exact (SupportPair.quotient_symm_symm _).symm
  · exact h.elim

 theorem symm_trans_assoc {X : Type*} [TopologicalSpace X] {a b c : X}
    (P : Path.Homotopic.Quotient a b) (R : Path.Homotopic.Quotient b c) :
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm P)
      (Path.Homotopic.Quotient.trans P R) = R := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

 theorem opposite_square {X : Type*} [TopologicalSpace X] {a b c d : X}
    (A : Path.Homotopic.Quotient a b) (B : Path.Homotopic.Quotient c b)
    (C : Path.Homotopic.Quotient c d) (D : Path.Homotopic.Quotient a d)
    (h : Path.Homotopic.Quotient.trans A
      (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm B)
        (Path.Homotopic.Quotient.trans C (Path.Homotopic.Quotient.symm D))) =
      Path.Homotopic.Quotient.refl a) :
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm A)
      (Path.Homotopic.Quotient.trans D
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm C) B)) =
      Path.Homotopic.Quotient.refl b := by
  have hrot := congrArg (fun R => Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.symm A) (Path.Homotopic.Quotient.trans R A)) h
  simp only [Path.Homotopic.Quotient.trans_assoc, symm_trans_assoc,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.symm_trans] at hrot
  have hinv := congrArg Path.Homotopic.Quotient.symm hrot
  simpa only [SupportPair.quotient_symm_trans, SupportPair.quotient_symm_symm,
    SupportPair.quotient_refl_symm, Path.Homotopic.Quotient.trans_assoc] using hinv

theorem doubleEdgeClass_four {a : V ⊕ V} (p : H.bipartiteDoubleCover.Walk a a)
    (hp : p.length = 4) : walkClass H.bipartiteDoubleCover (doublePoint H s hs)
      (doubleEdgeClass H s hs) p = Path.Homotopic.Quotient.refl (doublePoint H s hs a) := by
  cases p with
  | nil => simp at hp
  | @cons a b _ hab p =>
    cases p with
    | nil => simp at hp
    | @cons _ c _ hbc p =>
      cases p with
      | nil => simp at hp
      | @cons _ d _ hcd p =>
        cases p with
        | nil => simp at hp
        | @cons _ e _ hde p =>
          cases p with
          | cons h p => simp only [SimpleGraph.Walk.length_cons] at hp; omega
          | nil =>
            cases a with
            | inl v =>
              cases b with
              | inl w => exact hab.elim
              | inr w =>
                cases c with
                | inr x => exact hbc.elim
                | inl x =>
                  cases d with
                  | inl y => exact hcd.elim
                  | inr y =>
                    simpa only [walkClass_cons, walkClass_nil, doubleEdgeClass, doublePoint,
                      Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_assoc]
                      using SupportPair.doubleCover_four_null H (hs v) (hs w) (hs x) (hs y)
                        hab hbc.symm hcd hde.symm
            | inr v =>
              cases b with
              | inr w => exact hab.elim
              | inl w =>
                cases c with
                | inl x => exact hbc.elim
                | inr x =>
                  cases d with
                  | inr y => exact hcd.elim
                  | inl y =>
                    have h := SupportPair.doubleCover_four_null H (hs w) (hs v) (hs y) (hs x)
                      hab.symm hde hcd.symm hbc
                    simp only [Path.Homotopic.Quotient.trans_assoc] at h
                    have h' := opposite_square _ _ _ _ h
                    simpa only [walkClass_cons, walkClass_nil, doubleEdgeClass, doublePoint,
                      Path.Homotopic.Quotient.trans_refl] using h'

/-- The actual support-space edge realization fills all defining reduced
homotopy relations of the bipartite graph double cover. -/
def doubleCoverReducedEdgeClasses :
    ReducedEdgeClasses H.bipartiteDoubleCover (doublePoint H s hs) where
  edge := doubleEdgeClass H s hs
  reverse := fun {_ _} h => doubleEdgeClass_reverse H s hs h
  four := fun {_} p hp => doubleEdgeClass_four H s hs p hp



end

end AbelianTargets


