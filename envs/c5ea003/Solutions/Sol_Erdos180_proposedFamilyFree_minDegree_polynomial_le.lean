-- Prove2me | solution 1 for Erdos180.proposedFamilyFree_minDegree_polynomial_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:03:06.596627+00:00
-- url     : https://prove2.me/submissions/99eac337-8d8e-42e3-9007-335c6c1926a0

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Theorems.Thm_Erdos180_card_nonbacktrackingNeighbor
import Theorems.Thm_Erdos180_fintype_card_sigma_lower
import Theorems.Thm_Erdos180_kQuotient_mem_proposedFamily
import Theorems.Thm_Erdos180_mem_gammaBadVertices
import Theorems.Thm_Erdos180_proposedFamilyFree_four_cycle
import Theorems.Thm_Erdos180_proposedFamilyFree_six_cycle
import Theorems.Thm_Erdos180_quantitative_bad_vertex_heavy_triple_bound

namespace Erdos180

noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_nonbacktrackingThreePath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    G.degree u * (d - 1) ^ 2 ≤
      Fintype.card (NonbacktrackingThreePath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hsecond (a : G.neighborSet u) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            NonbacktrackingNeighbor G (a : V) (w : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · intro w
      exact hstep w.property.1.symm
  have hroot : G.degree u ≤ Fintype.card (G.neighborSet u) := by
    exact (G.card_neighborSet_eq_degree u).symm.le
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        NonbacktrackingNeighbor G (a : V) (w : V))
    hroot hsecond
  simpa [pow_two] using hcount

omit [Fintype V] in
lemma nonbacktrackingThreePathEndpoint_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingThreePathEndpoint G (u := u)) := by
  rintro ⟨a, w, b⟩ ⟨a', w', b'⟩ hb
  change (b : V) = (b' : V) at hb
  have haa : (a : V) = (a' : V) := by
    by_contra hne
    have hww : (w : V) ≠ (w' : V) := by
      intro heq
      have hwa' : G.Adj (w : V) (a' : V) :=
        Eq.mp
          (congrArg (fun x : V => G.Adj x (a' : V)) heq.symm)
          w'.property.1.symm
      have heqa : (a : V) = (a' : V) :=
        common_neighbor_unique_of_four_cycle_free hfour
          w.property.2.symm
          a.property w.property.1.symm
          a'.property hwa'
      exact hne heqa
    have hwb : G.Adj (w' : V) (b : V) :=
      Eq.mp (congrArg (G.Adj (w' : V)) hb.symm)
        b'.property.1
    have htriangle := common_neighbors_triangle_eq_of_cycle_free
      hbip hfour hsix
      w.property.2.symm hww w'.property.2.symm
      a.property w.property.1.symm
      b.property.1 hwb
      w'.property.1.symm a'.property
    exact b.property.2 htriangle.1.symm
  have ha : a = a' := Subtype.ext haa
  subst a'
  have hwb' : G.Adj (b : V) (w' : V) :=
    Eq.mp (congrArg (fun x : V => G.Adj x (w' : V)) hb.symm)
      b'.property.1.symm
  have hww : (w : V) = (w' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      b.property.2.symm
      w.property.1 b.property.1.symm
      w'.property.1 hwb'
  have hw : w = w' := Subtype.ext hww
  subst w'
  have hb' : b = b' := Subtype.ext hb
  subst b'
  rfl

theorem girthEight_degree_mul_pred_sq_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v)
    (u : V) :
    G.degree u * (d - 1) ^ 2 ≤ Fintype.card V := by
  calc
    G.degree u * (d - 1) ^ 2 ≤
        Fintype.card (NonbacktrackingThreePath G u) :=
      card_nonbacktrackingThreePath_lower G d hdegree u
    _ ≤ Fintype.card V :=
      Fintype.card_le_of_injective
        (nonbacktrackingThreePathEndpoint G)
        (nonbacktrackingThreePathEndpoint_injective
          G hbip hfour hsix)

end

noncomputable section
open SimpleGraph

lemma kernelNormalForm_kAdmissible
    {V : Type*} (g : KVertex → V)
    (hcolor : ∀ u v, g u = g v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v : KVertex | v.1 = copy}) :
    KAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

theorem proposedFamilyFree_no_kTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : kTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) : False := by
  let f := kernelNormalForm hom
  have hf : KAdmissible f :=
    kernelNormalForm_kAdmissible hom hcolor hcopies
  have hmember := kQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph kTemplate f) host
    (kernelQuotientCopy kTemplate host hom)⟩

end

noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma gamma_base_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma gamma_center_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gammaCopy_vertex_color_false_iff
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (witness : SimpleGraph.Copy gammaGraph G)
    (vertex : SubdivisionVertex 3) :
    subdivisionColor 3 vertex = false ↔
      color (witness vertex) = color (witness kSpecifiedCenter) := by
  rcases vertex with (base | center) | pair
  · simp only [subdivisionColor, true_iff]
    exact bipartite_coloring_eq_of_common_neighbor color
      (witness.toHom.map_rel (gamma_base_pair_adj base 0))
      (witness.toHom.map_rel (gamma_center_pair_adj base 0))
  · simp only [subdivisionColor, true_iff]
    calc
      color (witness (.inl (.inr center))) =
          color (witness (.inl (.inl (0 : Fin 3)))) :=
        (bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 center))
          (witness.toHom.map_rel
            (gamma_center_pair_adj 0 center))).symm
      _ = color (witness kSpecifiedCenter) :=
        bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 0))
          (witness.toHom.map_rel (gamma_center_pair_adj 0 0))
  · rcases pair with ⟨base, center⟩
    simp only [subdivisionColor, Bool.true_eq_false, false_iff]
    intro heq
    have hbase :
        color (witness (.inl (.inl base))) =
          color (witness kSpecifiedCenter) :=
      bipartite_coloring_eq_of_common_neighbor color
        (witness.toHom.map_rel (gamma_base_pair_adj base 0))
        (witness.toHom.map_rel (gamma_center_pair_adj base 0))
    exact (color.valid
      (witness.toHom.map_rel (gamma_base_pair_adj base center)))
        (hbase.trans heq.symm)

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (index : Fin 2) :
    Set.InjOn (gluedKHom copies hjoining)
      {vertex : KVertex | vertex.1 = index} := by
  rintro ⟨leftIndex, leftVertex⟩ hleft
    ⟨rightIndex, rightVertex⟩ hright heq
  change leftIndex = index at hleft
  change rightIndex = index at hright
  subst leftIndex
  subst rightIndex
  change copies index leftVertex = copies index rightVertex at heq
  have hvertices := (copies index).injective heq
  subst rightVertex
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (color : G.Coloring (Fin 2))
    (vertex : KVertex) :
    kColor vertex = false ↔
      color (gluedKVertex copies vertex) =
        color (copies 0 kSpecifiedCenter) := by
  rcases vertex with ⟨index, vertex⟩
  fin_cases index
  · simpa [kColor, gluedKVertex] using
      (gammaCopy_vertex_color_false_iff color (copies 0) vertex)
  · have hvalid :
        color (copies 0 kSpecifiedCenter) ≠
          color (copies 1 kSpecifiedCenter) :=
        color.valid hjoining
    change
      (if (1 : Fin 2) = 0 then subdivisionColor 3 vertex
        else !(subdivisionColor 3 vertex)) = false ↔
        color (copies 1 vertex) = color (copies 0 kSpecifiedCenter)
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    cases hcolor : subdivisionColor 3 vertex
    · simp only [Bool.not_false, Bool.true_eq_false, false_iff]
      intro heq
      have hsame :
          color (copies 1 vertex) =
            color (copies 1 kSpecifiedCenter) :=
        (gammaCopy_vertex_color_false_iff
          color (copies 1) vertex).mp hcolor
      exact hvalid (heq.symm.trans hsame)
    · simp only [Bool.not_true, true_iff]
      have hdistinct :
          color (copies 1 vertex) ≠
            color (copies 1 kSpecifiedCenter) := by
        intro heq
        have hfalse :=
          (gammaCopy_vertex_color_false_iff
            color (copies 1) vertex).mpr heq
        simp [hcolor] at hfalse
      apply Fin.ext
      omega

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    ∀ left right,
      gluedKHom copies hjoining left =
        gluedKHom copies hjoining right →
      kColor left = kColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hhostColor :
      color (gluedKVertex copies left) =
        color (gluedKVertex copies right) :=
    congrArg color heq
  cases hleft : kColor left <;> cases hright : kColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mp hleft
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mpr
        (hhostColor.symm.trans hbase)
    simp [hright] at hfalse
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mp hright
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mpr
        (hhostColor.trans hbase)
    simp [hleft] at hfalse
  · rfl

theorem proposedFamilyFree_not_adj_gammaGood
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hu : GammaGood host u) (hv : GammaGood host v) :
    ¬ host.Adj u v := by
  obtain ⟨first, hfirst⟩ := hu
  obtain ⟨second, hsecond⟩ := hv
  intro hedge
  let copies : Fin 2 → SimpleGraph.Copy gammaGraph host :=
    ![first, second]
  have hjoining :
      host.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter) := by
    change host.Adj (first kSpecifiedCenter)
      (second kSpecifiedCenter)
    rwa [hfirst, hsecond]
  exact proposedFamilyFree_no_kTemplate hfree
    (gluedKHom copies hjoining)
    (gluedKHom_color_respecting hbip copies hjoining)
    (gluedKHom_injOn_marked_copy copies hjoining)

theorem proposedFamilyFree_edge_has_gammaBad
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hedge : host.Adj u v) :
    u ∈ gammaBadVertices host ∨ v ∈ gammaBadVertices host := by
  classical
  by_cases hu : GammaGood host u
  · right
    apply (mem_gammaBadVertices host v).mpr
    intro hv
    exact proposedFamilyFree_not_adj_gammaGood
      host hfree hbip hu hv hedge
  · left
    exact (mem_gammaBadVertices host u).mpr hu

lemma edgeFinset_card_le_sum_degree_of_vertex_cover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover : Finset V)
    (hcover : ∀ ⦃u v : V⦄, G.Adj u v →
      u ∈ cover ∨ v ∈ cover) :
    G.edgeFinset.card ≤ ∑ v ∈ cover, G.degree v := by
  classical
  have hsubset :
      G.edgeFinset ⊆ cover.biUnion (fun v => G.incidenceFinset v) := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hedge
      rcases hcover hadj with hu | hv
      · exact Finset.mem_biUnion.mpr
          ⟨u, hu, (G.mem_incidenceFinset u _).mpr
            (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨v, hv, (G.mem_incidenceFinset v _).mpr
            (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩
  calc
    G.edgeFinset.card ≤
        (cover.biUnion fun v => G.incidenceFinset v).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ v ∈ cover, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ cover, G.degree v := by
      simp

theorem proposedFamilyFree_edge_card_le_gammaBad_degree_sum
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite) :
    host.edgeFinset.card ≤
      ∑ v ∈ gammaBadVertices host, host.degree v :=
  edgeFinset_card_le_sum_degree_of_vertex_cover
    host (gammaBadVertices host)
    (fun _ _ hedge => proposedFamilyFree_edge_has_gammaBad
      host hfree hbip hedge)

theorem proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n := by
  classical
  calc
    host.edgeFinset.card * (d - 1) ^ 2 ≤
        (∑ u ∈ gammaBadVertices host, host.degree u) *
          (d - 1) ^ 2 :=
      Nat.mul_le_mul_right ((d - 1) ^ 2)
        (proposedFamilyFree_edge_card_le_gammaBad_degree_sum
          host hfree hbip)
    _ = ∑ u ∈ gammaBadVertices host,
        host.degree u * (d - 1) ^ 2 := by
      simp [Finset.sum_mul]
    _ ≤ ∑ _u ∈ gammaBadVertices host, n := by
      gcongr with u hu
      simpa using girthEight_degree_mul_pred_sq_le_card
        host hbip (proposedFamilyFree_four_cycle hfree)
        (proposedFamilyFree_six_cycle hfree) d hdegree u
    _ = (gammaBadVertices host).card * n := by simp

end

noncomputable section
open Finset SimpleGraph

lemma quantitative_minimum_degree_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    n * d ≤ 2 * host.edgeFinset.card := by
  simpa [SimpleGraph.sum_degrees_eq_twice_card_edges] using
    Finset.card_nsmul_le_sum Finset.univ
      (fun vertex : Fin n => host.degree vertex) d
      (fun vertex _ => hdegree vertex)

lemma quantitative_bad_vertex_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n :=
  proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    host hfree hbip d hdegree

end

end Erdos180

open Erdos180
open Finset SimpleGraph

theorem solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 ≤
      864 * (n : ℝ) ^ 5 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdegreeReal :
      (n : ℝ) * (d : ℝ) ≤ 2 * (host.edgeFinset.card : ℝ) := by
    exact_mod_cast quantitative_minimum_degree_edge_bound
      host d hdegree
  have hedgeReal :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 ≤
        ((gammaBadVertices host).card : ℝ) * (n : ℝ) := by
    exact_mod_cast quantitative_bad_vertex_edge_bound
      host hfree hbip d hdegree
  have hbadReal := quantitative_bad_vertex_heavy_triple_bound
    host hn hfree hbip d hdegree hthreshold
  have hedgePolynomial :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 6 := by
    calc
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
          (((gammaBadVertices host).card : ℝ) * (n : ℝ)) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) := by
        gcongr
      _ = (((gammaBadVertices host).card : ℝ) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) *
            (n : ℝ) := by ring
      _ ≤ (432 * (n : ℝ) ^ 5) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hbadReal (Nat.cast_nonneg n)
      _ = 432 * (n : ℝ) ^ 6 := by ring
  apply (mul_le_mul_iff_right₀ hnreal).mp
  calc
    (n : ℝ) *
        ((d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3) =
        ((n : ℝ) * (d : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ (2 * (host.edgeFinset.card : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      gcongr
    _ = 2 *
          ((host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ 2 * (432 * (n : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left hedgePolynomial (by norm_num)
    _ = (n : ℝ) * (864 * (n : ℝ) ^ 5) := by ring
