-- Prove2me | solution 1 for Arexychen.Erdos180.familiesTheoremStructural
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:39:40.108538+00:00
-- url     : https://prove2.me/submissions/32438c68-0687-458a-9ffc-940b6a3d704d

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
import Theorems.Thm_Arexychen_Erdos180_familyFree_edgeCount_le_const_of_star_matching_pair
import Theorems.Thm_Arexychen_Erdos180_isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
import Theorems.Thm_Arexychen_Erdos180_matchingConstruction_extremalFamily_eventually_half_le
import Theorems.Thm_Arexychen_Erdos180_oneEdgeConstruction_extremalFamily_eventually_one_le
import Theorems.Thm_Arexychen_Erdos180_starConstruction_extremalFamily_eventually_pred_le

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

/-- A bounded natural-valued function is `O(1)`. -/
private theorem isOConstant_of_forall_le (f : ℕ → ℕ) (C : ℕ)
    (hC : ∀ n, f n ≤ C) :
    IsOConstant f := by
  unfold IsOConstant
  refine IsBigO.of_bound (C : ℝ) (Filter.Eventually.of_forall ?_)
  intro n
  have hreal : (f n : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC n
  simpa using hreal









/-- An eventually positive natural-valued function is bounded below by a
positive constant, asymptotically. -/
private theorem isOmegaConstant_of_eventually_one_le (f : ℕ → ℕ)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f n) :
    (fun _ : ℕ => (1 : ℝ)) =O[atTop] (fun n : ℕ => (f n : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [hpos] with n hn
  have hreal : (1 : ℝ) ≤ (f n : ℝ) := by
    exact_mod_cast hn
  simpa using hreal

/-- A bounded natural-valued function that is eventually at least one is
`Θ(1)`. -/
private theorem isThetaConstant_of_forall_le_of_eventually_one_le
    (f : ℕ → ℕ) (C : ℕ)
    (hC : ∀ n, f n ≤ C)
    (hpos : ∀ᶠ n in atTop, 1 ≤ f n) :
    IsThetaConstant f := by
  unfold IsThetaConstant
  exact ⟨isOConstant_of_forall_le f C hC,
    isOmegaConstant_of_eventually_one_le f hpos⟩

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



/--
If every admissible `n`-vertex host graph has at most `C` edges, then the
`sSup`-defined extremal value is also at most `C`.
-/
private theorem extremalFamily_le_of_forall_edgeCount_le
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (C : ℕ)
    (hC : ∀ n (G : SimpleGraph (Fin n)), FamilyFree F G → edgeCount G ≤ C) :
    ∀ n, extremalFamily F n ≤ C := by
  intro n
  unfold extremalFamily
  refine nat_sSup_le_of_forall_le ?_
  intro m hm
  rcases hm with ⟨G, hfree, rfl⟩
  exact hC n G hfree





end Erdos180

end
end Arexychen

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w

private theorem extremalFamily_isOLinear_of_forest_member
    {ι : Type v} [Finite ι]
    (F : ι → FiniteSimpleGraph.{u}) (i : ι)
    (hforest : (F i).reduced.IsAcyclic) :
    IsOLinear (fun n : ℕ => extremalFamily F n) := by
  unfold IsOLinear
  have hToSingle :
      (fun n : ℕ => (extremalFamily F n : ℝ)) =O[atTop]
        (fun n : ℕ => ((F i).extremal n : ℝ)) := by
    refine IsBigO.of_bound (1 : ℝ) (Filter.Eventually.of_forall ?_)
    intro n
    have hreal :
        (extremalFamily F n : ℝ) ≤ ((F i).extremal n : ℝ) := by
      exact_mod_cast extremalFamily_le_extremal F i n
    simpa using hreal
  have hiO : IsOLinear (fun n : ℕ => (F i).extremal n) := by
    simpa [FiniteSimpleGraph.extremal, FiniteSimpleGraph.reduced] using
      (isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
        (F i).graph hforest)
  unfold IsOLinear at hiO
  exact hToSingle.trans hiO

private theorem families_star_matching_pair_Theta_one_structural
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (htwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hpair : FamilyContainsStarMatchingPair F) :
    IsThetaConstant (fun n : ℕ => extremalFamily F n) := by
  rcases familyFree_edgeCount_le_const_of_star_matching_pair F hpair with ⟨C, hC⟩
  have hUpper : ∀ n, extremalFamily F n ≤ C :=
    extremalFamily_le_of_forall_edgeCount_le F C hC
  exact isThetaConstant_of_forall_le_of_eventually_one_le
    (fun n : ℕ => extremalFamily F n) C hUpper
    (oneEdgeConstruction_extremalFamily_eventually_one_le F htwo)

private theorem families_no_star_matching_pair_structural
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hforest : ∀ i : ι, (F i).reduced.IsAcyclic)
    (htwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated)
    (hno : ¬ FamilyContainsStarMatchingPair F) :
    IsThetaLinear (fun n : ℕ => extremalFamily F n) := by
  classical
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  have hUpper : IsOLinear (fun n : ℕ => extremalFamily F n) :=
    extremalFamily_isOLinear_of_forest_member F i0 (hforest i0)
  have hLower : IsOmegaLinear (fun n : ℕ => extremalFamily F n) := by
    by_cases hStar : ∃ i : ι, (F i).starAfterDeletingIsolated
    · have hNoMatching : ∀ j : ι, ¬ (F j).matchingAfterDeletingIsolated := by
        intro j hj
        rcases hStar with ⟨i, hi⟩
        exact hno ⟨⟨i, ⟨hi, htwo i⟩⟩, ⟨j, ⟨hj, htwo j⟩⟩⟩
      exact isOmegaLinear_of_eventually_half_le
        (fun n : ℕ => extremalFamily F n)
        (matchingConstruction_extremalFamily_eventually_half_le
          F htwo hNoMatching)
    · have hNoStar : ∀ i : ι, ¬ (F i).starAfterDeletingIsolated := by
        intro i hi
        exact hStar ⟨i, hi⟩
      exact isOmegaLinear_of_eventually_pred_le
        (fun n : ℕ => extremalFamily F n)
        (starConstruction_extremalFamily_eventually_pred_le
          F htwo hNoStar)
  exact isThetaLinear_of_isOLinear_of_isOmegaLinear
    (fun n : ℕ => extremalFamily F n) hUpper hLower

end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/-- Structural dichotomy theorem for finite families whose reduced members are
forests with at least two edges. -/
theorem solution
    {ι : Type v} [Finite ι] [Nonempty ι]
    (F : ι → FiniteSimpleGraph.{u})
    (hforest : ∀ i : ι, ((F i).reduced).IsAcyclic)
    (htwo : ∀ i : ι, (F i).atLeastTwoEdgesAfterDeletingIsolated) :
    (FamilyContainsStarMatchingPair F ∧
        IsThetaConstant (fun n : ℕ => extremalFamily F n)) ∨
      (¬ FamilyContainsStarMatchingPair F ∧
        IsThetaLinear (fun n : ℕ => extremalFamily F n)) := by
  by_cases hpair : FamilyContainsStarMatchingPair F
  · exact Or.inl
      ⟨hpair, families_star_matching_pair_Theta_one_structural F htwo hpair⟩
  · exact Or.inr
      ⟨hpair, families_no_star_matching_pair_structural F hforest htwo hpair⟩
end
namespace Arexychen
noncomputable section
namespace Erdos180




end Erdos180

end
end Arexychen
