-- Prove2me | Definitions.Def_AT260939824_SupportTorsion
-- name    : AT260939824_SupportTorsion
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:23:11.808387+00:00
-- url     : https://prove2.me/theorems/c180cf84-c036-4659-bcaa-4af77008739b
-- title:
--   Odd support paths, swapped return paths, and loop powers
-- statement:
--   Let $H$ be a finite graph with a chosen neighbor $s(v)$ at every vertex. An odd closed walk $\gamma$ at $a$ lifts to a path $\alpha:p\to\tau p$ in the support complex, with $p=(\delta_a,\delta_{s(a)})$, because its lift switches sheets an odd number of times. Define the return path by pointwise shore swap, and the alternating loop by
--   $$\beta(t)=\tau(\alpha(t)),\qquad P=\alpha*\beta.$$
--   For any based topological loop, define $P^0$ to be constant and $P^{n+1}=P*P^n$. The bundle also records relative path homotopy with explicit endpoint equalities, so lifts with propositionally equal endpoints can be compared without hiding endpoint transport.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SupportTorsion.lean, selected declaration lines 18-20, 101-103, 105-112, 114-117, 119-120, 137-139; SHA-256 bc56ae188a2ab135f302fa89006df5a041dd53f1baff9e1aeb3889a6ad3739a9. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_DoubleCoverSupport
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
# Odd torsion walks and support-space paths

This file makes the endpoint transports in the path-lifting argument of
Lemma 6.2 and Proposition 7.1 explicit.
-/

namespace AbelianTargets

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- A relative path homotopy after explicit transport of the two endpoints. -/
def HeteroPathHomotopic {a b a' b' : X} (P : Path a b) (Q : Path a' b') : Prop :=
  ∃ (ha : a' = a) (hb : b' = b), (P.cast ha hb).Homotopic Q

namespace HeteroPathHomotopic















end HeteroPathHomotopic

variable {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → V) (hs : ∀ v, H.Adj v (s v))







theorem toggleSheet_odd {n : ℕ} (hn : Odd n) (σ : Bool) : toggleSheet n σ = !σ := by
  rw [toggleSheet_eq_mod, Nat.odd_iff.mp hn]
  simp

/-- The path `α : p → τp` obtained from an odd closed graph walk. -/
def oddSupportPath {a : V} (γ : H.Walk a a) (hodd : Odd γ.length) :
    Path (SupportPair.vertex H (hs a)) (SupportPair.swap H (SupportPair.vertex H (hs a))) :=
  (supportLiftPath H s hs γ false).cast rfl (by
    change doublePoint H s hs (sheetVertex a true) =
      doublePoint H s hs (sheetVertex a (toggleSheet γ.length false))
    rw [toggleSheet_odd hodd]
    rfl)

/-- The return path is the shore swap of `α`. -/
def swappedReturnPath {p : SupportPair H} (α : Path p (SupportPair.swap H p)) :
    Path (SupportPair.swap H p) p :=
  (α.map (SupportPair.continuous_swap H)).cast rfl (SupportPair.swap_swap H p).symm

def alternatingSupportLoop {p : SupportPair H} (α : Path p (SupportPair.swap H p)) : Path p p :=
  α.trans (swappedReturnPath H α)



def pathLoopPower {p : X} (P : Path p p) : ℕ → Path p p
  | 0 => Path.refl p
  | n + 1 => P.trans (pathLoopPower P n)













end

end AbelianTargets


