-- Prove2me | solution 1 for AbelianTargets.oddSupportPath_torsion
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:13:51.976792+00:00
-- url     : https://prove2.me/submissions/9c3211a5-593d-4be4-b471-e58f2e777a59

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_DoubleCoverSupport
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportTorsion
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
import Theorems.Thm_AbelianTargets_ReducedHomotopic_lift_to_doubleCover
import Theorems.Thm_AbelianTargets_supportLiftPath_swap

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.ReducedWalks
section
/-!
# Reduced graph-walk homotopy and parity

This file formalizes the walk presentation in §2.2 of arXiv:2609.39824.
`ReducedHomotopic` is the smallest equivalence compatible with concatenation
which deletes spurs and closed walks of length four. Its restriction to closed
walks is the reduced homotopy relation used by the paper.

The statements `HasOddInvolution` and `HasOddTorsion` express the hypotheses
of Theorem 1.4 and Proposition 7.1 directly in this walk presentation.
The geometric construction of continuous graph homomorphisms is separate.
-/

namespace AbelianTargets

universe u
variable {V : Type u} (H : SimpleGraph V)



namespace ReducedHomotopic

variable {H}















end ReducedHomotopic



variable {H}











/-- Addition of exponents is concatenation of powers. -/
theorem loopPower_add {b : V} (γ : H.Walk b b) (m n : ℕ) :
    loopPower H γ (m + n) = (loopPower H γ m).append (loopPower H γ n) := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, ih, SimpleGraph.Walk.append_assoc]





/-- Any trivial concatenation power of an odd walk has even exponent.
The positivity hypothesis is unnecessary for this parity implication. -/
theorem even_exponent_of_odd_null_power {b : V} {γ : H.Walk b b} {N : ℕ}
    (hodd : Odd γ.length)
    (hnull : ReducedHomotopic H (loopPower H γ N) .nil) : Even N := by
  have hpar := hnull.length_mod_two
  simp only [loopPower_length, SimpleGraph.Walk.length_nil, Nat.zero_mod] at hpar
  rw [Nat.odd_iff] at hodd
  rw [Nat.mul_mod, hodd] at hpar
  simp only [Nat.mul_one, Nat.mod_mod] at hpar
  exact Nat.even_iff.mpr hpar





















namespace ReducedFundamentalGroup

variable (H) (b : V)





variable {H b}























end ReducedFundamentalGroup









end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.TopologicalWalks
section
/-!
# Passing the reduced walk presentation to topological path classes

This file proves the presentation argument used in Lemma 6.2.  A realization
of graph edges in a space, respecting reversal and filling every four-walk,
factors through the reduced graph-walk homotopy relation.  The geometric
edge maps and fillings themselves are constructed in `SupportGeometry`.
-/

namespace AbelianTargets

noncomputable section

variable {V X : Type*} [TopologicalSpace X] (H : SimpleGraph V) (f : V → X)













theorem walkPath_class (E : EdgePaths H f) {a b : V} (p : H.Walk a b) :
    Path.Homotopic.Quotient.mk (walkPath H f E p) =
      walkClass H f (fun {_ _} h => Path.Homotopic.Quotient.mk (E h)) p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simpa only [walkPath, walkClass_cons, Path.Homotopic.Quotient.mk_trans] using
      congrArg (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (E h))) ih

theorem walkPath_copy (E : EdgePaths H f) {a b a' b' : V} (p : H.Walk a b)
    (ha : a = a') (hb : b = b') :
    walkPath H f E (p.copy ha hb) =
      (walkPath H f E p).cast (congrArg f ha.symm) (congrArg f hb.symm) := by
  subst a'
  subst b'
  rfl

theorem walkPath_append (E : EdgePaths H f) {a b c : V}
    (p : H.Walk a b) (q : H.Walk b c) :
    (walkPath H f E (p.append q)).Homotopic
      ((walkPath H f E p).trans (walkPath H f E q)) := by
  induction p with
  | nil => exact (Path.Homotopic.refl_trans _).symm
  | cons h p ih =>
    exact ((Path.Homotopic.refl (E h)).hcomp (ih q)).trans
      (Path.Homotopic.trans_assoc _ _ _).symm

theorem walkClass_append (E : EdgeClasses H f) {a b c : V}
    (p : H.Walk a b) (q : H.Walk b c) :
    walkClass H f E (p.append q) =
      Path.Homotopic.Quotient.trans (walkClass H f E p) (walkClass H f E q) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [SimpleGraph.Walk.cons_append, walkClass_cons, ih,
      Path.Homotopic.Quotient.trans_assoc]



namespace ReducedEdgeClasses

variable {H f}

/-- Every generator of reduced walk homotopy becomes an actual equality of
topological path homotopy classes. -/
theorem respects_reducedHomotopic (E : ReducedEdgeClasses H f)
    {a b : V} {p q : H.Walk a b} (hpq : ReducedHomotopic H p q) :
    walkClass H f E.edge p = walkClass H f E.edge q := by
  induction hpq with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | append _ _ ih₁ ih₂ => simp only [walkClass_append, ih₁, ih₂]
  | spur h =>
    simp only [walkClass_cons, walkClass_nil, Path.Homotopic.Quotient.trans_refl]
    rw [E.reverse h]
    exact Path.Homotopic.Quotient.trans_symm _
  | four p hp => exact E.four p hp



end ReducedEdgeClasses

end

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.DoubleCoverSupport
section
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







theorem doubleEdgePath_class {a b : V ⊕ V} (h : H.bipartiteDoubleCover.Adj a b) :
    Path.Homotopic.Quotient.mk (doubleEdgePath H s hs h) = doubleEdgeClass H s hs h := by
  cases a <;> cases b
  · exact h.elim
  · rfl
  · rfl
  · exact h.elim

theorem doubleWalkPath_class {a b : V ⊕ V} (p : H.bipartiteDoubleCover.Walk a b) :
    Path.Homotopic.Quotient.mk (walkPath H.bipartiteDoubleCover (doublePoint H s hs)
      (doubleEdgePath H s hs) p) =
      walkClass H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgeClass H s hs) p := by
  have he : (fun {_ _} h => Path.Homotopic.Quotient.mk (doubleEdgePath H s hs h)) =
      doubleEdgeClass H s hs := by
    funext a b h
    exact doubleEdgePath_class H s hs h
  simpa only [he] using walkPath_class H.bipartiteDoubleCover (doublePoint H s hs)
    (doubleEdgePath H s hs) p











theorem doubleCover_respects_reducedHomotopic {a b : V ⊕ V}
    {p q : H.bipartiteDoubleCover.Walk a b}
    (hpq : ReducedHomotopic H.bipartiteDoubleCover p q) :
    walkClass H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgeClass H s hs) p =
      walkClass H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgeClass H s hs) q :=
  (doubleCoverReducedEdgeClasses H s hs).respects_reducedHomotopic hpq

end

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.DoubleCoverLifts
section
/-!
# Binary lifts of graph walks

Walks lift to the bipartite double cover with the sheet determined by their
length parity.  This is the combinatorial covering step in Lemma 6.2.
-/

namespace AbelianTargets

variable {V : Type*} (H : SimpleGraph V)






theorem toggleSheet_add (m n : ℕ) (b : Bool) :
    toggleSheet (m+n) b = toggleSheet n (toggleSheet m b) := by
  induction m generalizing b with
  | zero => simp
  | succ m ih => simpa [Nat.succ_add] using ih (!b)













theorem liftWalk_append {a b c : V} (p : H.Walk a b) (q : H.Walk b c) (σ : Bool) :
    (liftWalk H p σ).append (liftWalk H q (toggleSheet p.length σ)) =
      (liftWalk H (p.append q) σ).copy rfl
        (congrArg (sheetVertex c) (by
          simpa only [SimpleGraph.Walk.length_append] using toggleSheet_add p.length q.length σ)) := by
  induction p generalizing σ with
  | nil => rfl
  | cons h p ih =>
    simpa only [SimpleGraph.Walk.cons_append, liftWalk, SimpleGraph.Walk.length_cons,
      toggleSheet_succ, SimpleGraph.Walk.copy_cons] using
      congrArg (SimpleGraph.Walk.cons (liftedEdge H h σ)) (ih q (!σ))

namespace ReducedHomotopic

variable {H}



end ReducedHomotopic



namespace HeteroReducedHomotopic

variable {H}









end HeteroReducedHomotopic

theorem liftWalk_append_hetero {a b c : V}
    (p : H.Walk a b) (q : H.Walk b c) (σ : Bool) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H (p.append q) σ)
      ((liftWalk H p σ).append (liftWalk H q (toggleSheet p.length σ))) := by
  refine ⟨rfl, congrArg (sheetVertex c) (by
    simpa only [SimpleGraph.Walk.length_append] using toggleSheet_add p.length q.length σ), ?_⟩
  rw [← liftWalk_append H p q σ]
  exact .refl _









noncomputable section

variable [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))







end

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.SupportTorsion
section
/-!
# Odd torsion walks and support-space paths

This file makes the endpoint transports in the path-lifting argument of
Lemma 6.2 and Proposition 7.1 explicit.
-/

namespace AbelianTargets

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X : Type*} [TopologicalSpace X]



namespace HeteroPathHomotopic



theorem of_homotopic {a b : X} {P Q : Path a b} (h : P.Homotopic Q) :
    HeteroPathHomotopic P Q := ⟨rfl, rfl, h⟩

theorem symm {a b a' b' : X} {P : Path a b} {Q : Path a' b'}
    (h : HeteroPathHomotopic P Q) : HeteroPathHomotopic Q P := by
  rcases h with ⟨ha, hb, h⟩
  subst a'
  subst b'
  exact ⟨rfl, rfl, h.symm⟩

theorem trans {a b a' b' a'' b'' : X}
    {P : Path a b} {Q : Path a' b'} {R : Path a'' b''}
    (hPQ : HeteroPathHomotopic P Q) (hQR : HeteroPathHomotopic Q R) :
    HeteroPathHomotopic P R := by
  rcases hPQ with ⟨ha, hb, hPQ⟩
  rcases hQR with ⟨ha', hb', hQR⟩
  subst a'
  subst b'
  subst a''
  subst b''
  exact ⟨rfl, rfl, hPQ.trans hQR⟩

theorem append {a b c a' b' c' : X}
    {P : Path a b} {Q : Path a' b'} {R : Path b c} {S : Path b' c'}
    (hPQ : HeteroPathHomotopic P Q) (hRS : HeteroPathHomotopic R S) :
    HeteroPathHomotopic (P.trans R) (Q.trans S) := by
  rcases hPQ with ⟨ha, hb, hPQ⟩
  rcases hRS with ⟨_, hc, hRS⟩
  subst a'
  subst b'
  subst c'
  exact ⟨rfl, rfl, hPQ.hcomp hRS⟩

theorem of_pointwise_eq {a b a' b' : X} (P : Path a b) (Q : Path a' b')
    (h : ∀ t, P t = Q t) : HeteroPathHomotopic P Q := by
  have ha : a' = a := by simpa only [Path.source] using (h 0).symm
  have hb : b' = b := by simpa only [Path.target] using (h 1).symm
  refine ⟨ha, hb, ?_⟩
  have he : P.cast ha hb = Q := Path.ext (funext h)
  rw [he]

theorem homotopic {a b : X} {P Q : Path a b} (h : HeteroPathHomotopic P Q) : P.Homotopic Q := by
  rcases h with ⟨_, _, h⟩
  exact h

end HeteroPathHomotopic

variable {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → V) (hs : ∀ v, H.Adj v (s v))

theorem supportHeteroReducedHomotopic {a b a' b' : V ⊕ V}
    {p : H.bipartiteDoubleCover.Walk a b} {q : H.bipartiteDoubleCover.Walk a' b'}
    (hpq : HeteroReducedHomotopic H.bipartiteDoubleCover p q) :
    HeteroPathHomotopic
      (walkPath H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) p)
      (walkPath H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) q) := by
  rcases hpq with ⟨ha, hb, hpq⟩
  refine ⟨congrArg (doublePoint H s hs) ha.symm, congrArg (doublePoint H s hs) hb.symm, ?_⟩
  rw [← walkPath_copy H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) p ha hb]
  apply Path.Homotopic.Quotient.exact
  rw [doubleWalkPath_class, doubleWalkPath_class]
  exact doubleCover_respects_reducedHomotopic H s hs hpq

theorem supportLiftPath_append {a b c : V} (p : H.Walk a b) (q : H.Walk b c) (σ : Bool) :
    HeteroPathHomotopic (supportLiftPath H s hs (p.append q) σ)
      ((supportLiftPath H s hs p σ).trans (supportLiftPath H s hs q (toggleSheet p.length σ))) :=
  (supportHeteroReducedHomotopic H s hs (liftWalk_append_hetero H p q σ)).trans
    (.of_homotopic (walkPath_append H.bipartiteDoubleCover (doublePoint H s hs)
      (doubleEdgePath H s hs) (liftWalk H p σ) (liftWalk H q (toggleSheet p.length σ))))

theorem supportLiftPath_reducedHomotopic {a b : V} {p q : H.Walk a b}
    (hpq : ReducedHomotopic H p q) (σ : Bool) :
    HeteroPathHomotopic (supportLiftPath H s hs p σ) (supportLiftPath H s hs q σ) :=
  supportHeteroReducedHomotopic H s hs (ReducedHomotopic.lift_to_doubleCover H hpq σ)









theorem supportLiftPath_double_odd {a : V} (γ : H.Walk a a) (hodd : Odd γ.length) :
    HeteroPathHomotopic (supportLiftPath H s hs (γ.append γ) false)
      (alternatingSupportLoop H (oddSupportPath H s hs γ hodd)) := by
  have hα : HeteroPathHomotopic (supportLiftPath H s hs γ false)
      (oddSupportPath H s hs γ hodd) := .of_pointwise_eq _ _ (fun _ => rfl)
  have hβ : HeteroPathHomotopic (supportLiftPath H s hs γ (toggleSheet γ.length false))
      (swappedReturnPath H (oddSupportPath H s hs γ hodd)) := by
    apply HeteroPathHomotopic.of_pointwise_eq
    intro t
    change supportLiftPath H s hs γ (toggleSheet γ.length false) t =
      SupportPair.swap H (supportLiftPath H s hs γ false t)
    exact (congrArg (fun sheet : Bool => supportLiftPath H s hs γ sheet t)
      (toggleSheet_odd hodd false)).trans (supportLiftPath_swap H s hs γ false t).symm
  exact (supportLiftPath_append H s hs γ γ false).trans (hα.append hβ)



theorem toggleSheet_even {n : ℕ} (hn : Even n) (σ : Bool) : toggleSheet n σ = σ := by
  rw [toggleSheet_eq_mod, Nat.even_iff.mp hn]
  simp

theorem supportLiftPath_loopPower {a : V} (δ : H.Walk a a) (hδ : Even δ.length)
    (σ : Bool) (P : Path (doublePoint H s hs (sheetVertex a σ))
      (doublePoint H s hs (sheetVertex a σ)))
    (hP : HeteroPathHomotopic (supportLiftPath H s hs δ σ) P) (n : ℕ) :
    HeteroPathHomotopic (supportLiftPath H s hs (loopPower H δ n) σ) (pathLoopPower P n) := by
  induction n with
  | zero => exact .of_pointwise_eq _ _ (fun _ => rfl)
  | succ n ih =>
    have ht : HeteroPathHomotopic (supportLiftPath H s hs (loopPower H δ n) (toggleSheet δ.length σ))
        (supportLiftPath H s hs (loopPower H δ n) σ) := by
      apply HeteroPathHomotopic.of_pointwise_eq
      intro t
      rw [toggleSheet_even hδ]
    exact (supportLiftPath_append H s hs δ (loopPower H δ n) σ).trans
      (hP.append (ht.trans ih))

omit [Fintype V] in
theorem loopPower_double {a : V} (γ : H.Walk a a) (n : ℕ) :
    loopPower H (γ.append γ) n = loopPower H γ (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loopPower_succ, ih, Nat.mul_succ]
    rw [show 2*n+2 = 2+2*n by omega, loopPower_add]
    simp [loopPower_succ]







end

end AbelianTargets

end

/-!
# Odd torsion walks and support-space paths

This file makes the endpoint transports in the path-lifting argument of
Lemma 6.2 and Proposition 7.1 explicit.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X]
variable {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → V) (hs : ∀ v, H.Adj v (s v))

theorem solution {a : V} (γ : H.Walk a a) (hodd : Odd γ.length)
    {N : ℕ} (hnull : ReducedHomotopic H (loopPower H γ N) .nil) :
    ∃ k : ℕ, N = 2*k ∧
      (pathLoopPower (alternatingSupportLoop H (oddSupportPath H s hs γ hodd)) k).Homotopic
        (Path.refl (SupportPair.vertex H (hs a))) := by
  obtain ⟨k, hk⟩ := even_exponent_of_odd_null_power hodd hnull
  have hN : N = 2*k := by omega
  have hδ : Even (γ.append γ).length := by
    simp only [SimpleGraph.Walk.length_append]
    exact ⟨γ.length, rfl⟩
  have hP := supportLiftPath_loopPower H s hs (γ.append γ) hδ false
    (alternatingSupportLoop H (oddSupportPath H s hs γ hodd))
    (supportLiftPath_double_odd H s hs γ hodd) k
  have hnull' : ReducedHomotopic H (loopPower H (γ.append γ) k) .nil := by
    simpa only [loopPower_double, ← hN] using hnull
  have hT := supportLiftPath_reducedHomotopic H s hs hnull' false
  exact ⟨k, hN, (hP.symm.trans hT).homotopic⟩
