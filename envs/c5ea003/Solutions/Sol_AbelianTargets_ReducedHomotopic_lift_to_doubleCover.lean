-- Prove2me | solution 1 for AbelianTargets.ReducedHomotopic.lift_to_doubleCover
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:08:16.914401+00:00
-- url     : https://prove2.me/submissions/f161348e-2fe7-42b7-a896-1306090bdf12

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
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



theorem toggleSheet_eq_of_mod_eq {m n : ℕ} (h : m % 2 = n % 2) (b : Bool) :
    toggleSheet m b = toggleSheet n b := by rw [toggleSheet_eq_mod, toggleSheet_eq_mod, h]









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

theorem refl {a b : V} (p : H.Walk a b) : HeteroReducedHomotopic H p p :=
  ⟨rfl, rfl, .refl p⟩

theorem symm {a b a' b' : V} {p : H.Walk a b} {q : H.Walk a' b'}
    (h : HeteroReducedHomotopic H p q) : HeteroReducedHomotopic H q p := by
  rcases h with ⟨ha, hb, h⟩
  subst a'
  subst b'
  exact ⟨rfl, rfl, h.symm⟩

theorem trans {a b a' b' a'' b'' : V}
    {p : H.Walk a b} {q : H.Walk a' b'} {r : H.Walk a'' b''}
    (hpq : HeteroReducedHomotopic H p q) (hqr : HeteroReducedHomotopic H q r) :
    HeteroReducedHomotopic H p r := by
  rcases hpq with ⟨ha, hb, hpq⟩
  rcases hqr with ⟨ha', hb', hqr⟩
  subst a'
  subst b'
  subst a''
  subst b''
  exact ⟨rfl, rfl, hpq.trans hqr⟩

theorem append {a b c a' b' c' : V}
    {p : H.Walk a b} {q : H.Walk a' b'} {r : H.Walk b c} {s : H.Walk b' c'}
    (hpq : HeteroReducedHomotopic H p q) (hrs : HeteroReducedHomotopic H r s) :
    HeteroReducedHomotopic H (p.append r) (q.append s) := by
  rcases hpq with ⟨ha, hb, hpq⟩
  rcases hrs with ⟨_, hc, hrs⟩
  subst a'
  subst b'
  subst c'
  exact ⟨rfl, rfl, .append hpq hrs⟩

end HeteroReducedHomotopic

theorem liftWalk_append_hetero {a b c : V}
    (p : H.Walk a b) (q : H.Walk b c) (σ : Bool) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H (p.append q) σ)
      ((liftWalk H p σ).append (liftWalk H q (toggleSheet p.length σ))) := by
  refine ⟨rfl, congrArg (sheetVertex c) (by
    simpa only [SimpleGraph.Walk.length_append] using toggleSheet_add p.length q.length σ), ?_⟩
  rw [← liftWalk_append H p q σ]
  exact .refl _

theorem liftWalk_changeSheet {a b : V} (p : H.Walk a b) {σ τ : Bool} (h : σ = τ) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H p σ) (liftWalk H p τ) := by
  subst τ
  exact .refl _







noncomputable section

variable [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))







end

end AbelianTargets

end

/-!
# Binary lifts of graph walks

Walks lift to the bipartite double cover with the sheet determined by their
length parity.  This is the combinatorial covering step in Lemma 6.2.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {V : Type*} (H : SimpleGraph V)
open AbelianTargets.ReducedHomotopic

theorem solution {a b : V} {p q : H.Walk a b}
    (hpq : ReducedHomotopic H p q) (σ : Bool) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H p σ) (liftWalk H q σ) := by
  induction hpq generalizing σ with
  | refl p => exact .refl _
  | symm _ ih => exact (ih σ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ σ).trans (ih₂ σ)
  | @append a b c p q r s hpq hrs ih₁ ih₂ =>
    have he : toggleSheet p.length σ = toggleSheet q.length σ :=
      toggleSheet_eq_of_mod_eq hpq.length_mod_two σ
    have htail : HeteroReducedHomotopic H.bipartiteDoubleCover
        (liftWalk H r (toggleSheet p.length σ)) (liftWalk H s (toggleSheet q.length σ)) := by
      exact (ih₂ (toggleSheet p.length σ)).trans (liftWalk_changeSheet H s he)
    exact (liftWalk_append_hetero H p r σ).trans
      (((ih₁ σ).append htail).trans (liftWalk_append_hetero H q s σ).symm)
  | spur h =>
    cases σ
    · exact ⟨rfl, rfl, .spur (liftedEdge H h false)⟩
    · exact ⟨rfl, rfl, .spur (liftedEdge H h true)⟩
  | @four a p hp =>
    have he : sheetVertex a (toggleSheet p.length σ) = sheetVertex a σ := by
      rw [hp]
      cases σ <;> rfl
    refine ⟨rfl, he, .four _ ?_⟩
    exact (SimpleGraph.Walk.length_copy (liftWalk H p σ) rfl he).trans
      ((liftWalk_length H p σ).trans hp)
