-- Prove2me | solution 1 for Arexychen.Erdos180.isThetaLinear_extremal_of_reduced_isAcyclic_of_atLeastTwo
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:30:46.764904+00:00
-- url     : https://prove2.me/submissions/7e96f6a3-6e5b-43b9-a0ce-f3b5d8f96086

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_finite
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic
import Theorems.Thm_Arexychen_Erdos180_isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
import Theorems.Thm_Arexychen_Erdos180_matchingConstruction_extremalFamily_eventually_half_le
import Theorems.Thm_Arexychen_Erdos180_starConstruction_extremalFamily_eventually_pred_le

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w















/-- Combine the two sides of a linear asymptotic estimate. -/
private theorem isThetaLinear_of_isOLinear_of_isOmegaLinear
    (f : ℕ → ℕ) (hO : IsOLinear f) (hΩ : IsOmegaLinear f) :
    IsThetaLinear f := by
  unfold IsThetaLinear IsOLinear IsOmegaLinear at *
  exact ⟨hO, hΩ⟩

/-- If `f(n) ≥ n - 1` eventually, then `f(n) = Ω(n)`. -/
private theorem isOmegaLinear_of_eventually_pred_le
    (f : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, n - 1 ≤ f n) :
    IsOmegaLinear f := by
  unfold IsOmegaLinear
  refine IsBigO.of_bound (2 : ℝ) ?_
  filter_upwards [h, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hpred hn2
  have hnat : n ≤ 2 * f n := by
    have hpred' : n ≤ 2 * (n - 1) := by omega
    exact hpred'.trans (Nat.mul_le_mul_left 2 hpred)
  have hreal : (n : ℝ) ≤ (2 : ℝ) * (f n : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal

/-- If `f(n) ≥ ⌊n/2⌋` eventually, then `f(n) = Ω(n)`. -/
private theorem isOmegaLinear_of_eventually_half_le
    (f : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, n / 2 ≤ f n) :
    IsOmegaLinear f := by
  unfold IsOmegaLinear
  refine IsBigO.of_bound (4 : ℝ) ?_
  filter_upwards [h, eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hhalf hn2
  have hnat : n ≤ 4 * f n := by
    have hhalf' : n ≤ 4 * (n / 2) := by omega
    exact hhalf'.trans (Nat.mul_le_mul_left 4 hhalf)
  have hreal : (n : ℝ) ≤ (4 : ℝ) * (f n : ℝ) := by
    exact_mod_cast hnat
  simpa using hreal


end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- The repository's `edgeCount` agrees with mathlib's finite edge finset count. -/
private theorem edgeCount_eq_edgeFinset_card
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]



/-- If every element of a set of natural numbers is at most `C`, then its
supremum is at most `C`.  This version also handles the empty set. -/
private theorem nat_sSup_le_of_forall_le {s : Set ℕ} {C : ℕ}
    (hC : ∀ m ∈ s, m ≤ C) :
    sSup s ≤ C := by
  classical
  rw [Nat.sSup_def ⟨C, hC⟩]
  exact Nat.find_min' ⟨C, hC⟩ hC

/-- Membership in a bounded set of natural numbers gives a lower bound on its
supremum. -/
private theorem nat_le_sSup_of_mem_of_forall_le {s : Set ℕ} {m C : ℕ}
    (hm : m ∈ s)
    (hC : ∀ x ∈ s, x ≤ C) :
    m ≤ sSup s := by
  exact le_csSup ⟨C, hC⟩ hm

/-- A graph on `n` labelled vertices has at most `n.choose 2` edges. -/
private theorem edgeCount_le_complete_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    edgeCount G ≤ n.choose 2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hedge : edgeCount G = G.edgeFinset.card :=
    edgeCount_eq_edgeFinset_card G
  rw [hedge]
  simpa using (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))

/-- Any admissible host contributes a lower bound to the single-graph extremal
number. -/
private theorem extremalNumber_ge_of_host {α : Type u}
    (H : SimpleGraph α) {n : ℕ}
    (G : SimpleGraph (Fin n))
    (hfree : IsHFree H G) :
    edgeCount G ≤ extremalNumber H n := by
  unfold extremalNumber
  refine nat_le_sSup_of_mem_of_forall_le (C := n.choose 2) ?_ ?_
  · exact ⟨G, hfree, rfl⟩
  · intro m hm
    rcases hm with ⟨G', _hfree, rfl⟩
    exact edgeCount_le_complete_bound G'


end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v w









/-- A family-free graph is, in particular, free of each chosen member of the
family, so the family extremal number is bounded above by each individual
extremal number. -/
private theorem extremalFamily_le_extremal
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (i : ι) :
    ∀ n, extremalFamily F n ≤ (F i).extremal n := by
  intro n
  unfold extremalFamily
  change sSup {m : ℕ |
      ∃ G : SimpleGraph (Fin n), FamilyFree F G ∧ edgeCount G = m} ≤
    extremalNumber (F i).graph n
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  exact extremalNumber_ge_of_host (F i).graph G (hfree i)









end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

attribute [local instance] SimpleGraph.neighborSetFintype

universe u v

































-- `[Fintype α]` is unused in the statement but required by the proof
-- (the witness constant is `Fintype.card α`), hence the linter override.




-- `[Fintype α]` is unused in the statement but required by the proof
-- (it applies the guarded bound above), hence the linter override.




private theorem edgeCount_starGraph_eq_degree_center
    {α : Type u} [Finite α] (c : α)
    [Fintype ((starGraph c).neighborSet c)] :
    edgeCount (starGraph c) = (starGraph c).degree c := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let G : SimpleGraph α := starGraph c
  have hinc : G.edgeFinset = G.incidenceFinset c := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [G, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_incidenceFinset,
          SimpleGraph.mk'_mem_incidenceSet_iff, SimpleGraph.mem_edgeSet, starGraph]
        constructor
        · intro hxy
          refine ⟨hxy, ?_⟩
          rcases hxy with hxy | hxy
          · exact Or.inl hxy.1.symm
          · exact Or.inr hxy.1.symm
        · intro hxy
          exact hxy.1
  calc
    edgeCount (starGraph c) = G.edgeFinset.card := by
      rw [edgeCount_eq_edgeFinset_card]
    _ = (G.incidenceFinset c).card := by rw [hinc]
    _ = G.degree c := SimpleGraph.card_incidenceFinset_eq_degree G c

private theorem degree_le_one_of_matchingGraph
    {α : Type u} (G : SimpleGraph α) (v : α)
    [Fintype (G.neighborSet v)]
    (hmatch : IsMatchingGraph G) :
    G.degree v ≤ 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_one_iff_subsingleton.mpr
    ⟨fun x y => Subtype.ext (hmatch x.property y.property)⟩

private theorem not_isMatchingGraph_of_isStar_of_two_edges
    {α : Type u} [Finite α] (G : SimpleGraph α)
    (hstar : IsStar G) (htwo : 2 ≤ edgeCount G) :
    ¬ IsMatchingGraph G := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  intro hmatch
  rcases hstar with ⟨c, rfl⟩
  letI : Fintype ((starGraph c).neighborSet c) :=
    Fintype.ofFinite ((starGraph c).neighborSet c)
  have hcount :
      edgeCount (starGraph c) = (starGraph c).degree c :=
    edgeCount_starGraph_eq_degree_center c
  have hdeg : (starGraph c).degree c ≤ 1 :=
    degree_le_one_of_matchingGraph (starGraph c) c hmatch
  omega

private theorem extremal_eventually_pred_le_of_not_star
    (H : FiniteSimpleGraph.{u})
    (htwo : H.atLeastTwoEdgesAfterDeletingIsolated)
    (hNoStar : ¬ H.starAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n - 1 ≤ H.extremal n := by
  let F : Unit → FiniteSimpleGraph.{u} := fun _ => H
  have hFam :
      ∀ᶠ n in atTop, n - 1 ≤ extremalFamily F n :=
    starConstruction_extremalFamily_eventually_pred_le
      F (by intro _; exact htwo) (by intro _; exact hNoStar)
  exact hFam.mono (fun n hn => by
    have hle : extremalFamily F n ≤ H.extremal n := by
      simpa [F] using extremalFamily_le_extremal F () n
    exact hn.trans hle)

private theorem extremal_eventually_half_le_of_star
    (H : FiniteSimpleGraph.{u})
    (hstar : H.starAfterDeletingIsolated)
    (htwo : H.atLeastTwoEdgesAfterDeletingIsolated) :
    ∀ᶠ n in atTop, n / 2 ≤ H.extremal n := by
  classical
  let F : Unit → FiniteSimpleGraph.{u} := fun _ => H
  letI : Fintype H.graph.support := Fintype.ofFinite H.graph.support
  letI : DecidableRel H.reduced.Adj := Classical.decRel _
  have hNoMatching : ∀ _ : Unit, ¬ (F ()).matchingAfterDeletingIsolated := by
    intro _
    exact not_isMatchingGraph_of_isStar_of_two_edges H.reduced hstar htwo
  have hFam :
      ∀ᶠ n in atTop, n / 2 ≤ extremalFamily F n :=
    matchingConstruction_extremalFamily_eventually_half_le
      F (by intro _; exact htwo) hNoMatching
  exact hFam.mono (fun n hn => by
    have hle : extremalFamily F n ≤ H.extremal n := by
      simpa [F] using extremalFamily_le_extremal F () n
    exact hn.trans hle)

end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180 in
theorem solution
    (H : FiniteSimpleGraph.{u})
    (hforest : H.reduced.IsAcyclic)
    (htwo : H.atLeastTwoEdgesAfterDeletingIsolated) :
    IsThetaLinear (fun n => H.extremal n) := by
  refine isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n => H.extremal n) ?_ ?_
  · simpa [FiniteSimpleGraph.extremal, FiniteSimpleGraph.reduced] using
      isOLinear_extremalNumber_of_deleteIsolated_isAcyclic H.graph hforest
  · by_cases hstar : H.starAfterDeletingIsolated
    · exact isOmegaLinear_of_eventually_half_le
        (fun n => H.extremal n)
        (extremal_eventually_half_le_of_star H hstar htwo)
    · exact isOmegaLinear_of_eventually_pred_le
        (fun n => H.extremal n)
        (extremal_eventually_pred_le_of_not_star H htwo hstar)
end
namespace Arexychen
noncomputable section
namespace Erdos180




end Erdos180

end
end Arexychen
