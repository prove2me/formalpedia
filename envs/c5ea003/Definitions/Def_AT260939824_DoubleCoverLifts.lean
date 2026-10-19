-- Prove2me | Definitions.Def_AT260939824_DoubleCoverLifts
-- name    : AT260939824_DoubleCoverLifts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:22:25.110169+00:00
-- url     : https://prove2.me/theorems/644bfcf6-2d65-42e9-9298-b5753a3603cb
-- title:
--   Binary lifts of graph walks
-- statement:
--   Let $H$ be a simple graph. A walk in $H$ lifts to its bipartite double cover after a starting sheet has been chosen; every edge switches sheets. For a walk $p$ of length $n$, the final sheet is the initial sheet toggled $n$ times. The construction includes explicit endpoint transports for reduced homotopy and the resulting paths in the support-pair space.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/DoubleCoverLifts.lean, selected declaration lines 14-16, 18-19, 27-33, 38-40, 42-44, 46-49, 51-55, 82-85, 195-198; SHA-256 4311ba9768820c9fa97996e3bf22ab1083a0785c1abf4704e0e9ae338e35fa1f. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverSupport
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AbelianTargets260939824ReducedWalks
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
# Binary lifts of graph walks

Walks lift to the bipartite double cover with the sheet determined by their
length parity.  This is the combinatorial covering step in Lemma 6.2.
-/

namespace AbelianTargets

variable {V : Type*} (H : SimpleGraph V)

def toggleSheet : ℕ → Bool → Bool
  | 0, b => b
  | n + 1, b => toggleSheet n (!b)

@[simp] theorem toggleSheet_zero (b : Bool) : toggleSheet 0 b = b := rfl
@[simp] theorem toggleSheet_succ (n : ℕ) (b : Bool) : toggleSheet (n+1) b = toggleSheet n (!b) := rfl



theorem toggleSheet_eq_mod (n : ℕ) (b : Bool) :
    toggleSheet n b = if n % 2 = 0 then b else !b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with hn | hn <;> simp [toggleSheet_succ, ih, Nat.add_mod, hn]



def sheetVertex (v : V) : Bool → V ⊕ V
  | false => .inl v
  | true => .inr v

def liftedEdge {a b : V} (h : H.Adj a b) (σ : Bool) :
    H.bipartiteDoubleCover.Adj (sheetVertex a σ) (sheetVertex b (!σ)) := by
  cases σ <;> exact h

def liftWalk : {a b : V} → (p : H.Walk a b) → (σ : Bool) →
    H.bipartiteDoubleCover.Walk (sheetVertex a σ) (sheetVertex b (toggleSheet p.length σ))
  | _, _, .nil, _ => .nil
  | _, _, .cons h p, σ => .cons (liftedEdge H h σ) (liftWalk p (!σ))

@[simp] theorem liftWalk_length {a b : V} (p : H.Walk a b) (σ : Bool) :
    (liftWalk H p σ).length = p.length := by
  induction p generalizing σ with
  | nil => rfl
  | cons h p ih => simpa [liftWalk] using ih (!σ)



namespace ReducedHomotopic

variable {H}



end ReducedHomotopic

/-- Reduced homotopy with endpoint equalities made explicit. This wrapper
allows lifting to a covering graph without hiding endpoint transports. -/
def HeteroReducedHomotopic {a b a' b' : V} (p : H.Walk a b) (q : H.Walk a' b') : Prop :=
  ∃ (ha : a = a') (hb : b = b'), ReducedHomotopic H (p.copy ha hb) q

namespace HeteroReducedHomotopic

variable {H}









end HeteroReducedHomotopic











noncomputable section

variable [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))

def supportLiftPath {a b : V} (p : H.Walk a b) (σ : Bool) :
    Path (doublePoint H s hs (sheetVertex a σ))
      (doublePoint H s hs (sheetVertex b (toggleSheet p.length σ))) :=
  walkPath H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) (liftWalk H p σ)





end

end AbelianTargets


