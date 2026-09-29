-- Prove2me | Definitions.Def_Shared_HypergraphTuranBoundedMatching_Construction
-- name    : Shared_HypergraphTuranBoundedMatching_Construction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:36:28.450322+00:00
-- url     : https://prove2.me/theorems/93831bb9-9ac9-4556-8d4b-e8f10a01fe99
-- title:
--   Aether Catalog definitions — Shared_HypergraphTuranBoundedMatching_Construction
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.HypergraphTuranBoundedMatching.Construction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/HypergraphTuranBoundedMatching/Construction.lean by skeleton subtraction
import Mathlib

/-! # The extremal construction for Berge-triangle-free 3-graphs

This file formalizes the lower-bound construction underlying the `r = 3` theorem
in *Hypergraph Turán with bounded matching number*.  There are `s` disjoint
spine-pairs and `t` outside vertices.  An edge consists of one spine-pair and
one outside vertex.  We prove that the construction is 3-uniform, has exactly
`s*t` edges, is Berge-triangle-free, and, when `s ≤ t`, has matching number
exactly `s`.  Taking `t = n - 2s` (and `n ≥ 3s`) gives `s(n-2s)` edges.
-/

open scoped Classical
open Finset

namespace HypergraphTuran

abbrev Vertex (s t : ℕ) := (Fin s × Bool) ⊕ Fin t
abbrev Hyperedge (s t : ℕ) := Finset (Vertex s t)
abbrev Hypergraph (s t : ℕ) := Finset (Hyperedge s t)

/-- The two private spine vertices belonging to index `i`. -/
def spinePair {s t : ℕ} (i : Fin s) : Hyperedge s t :=
  {Sum.inl (i, false), Sum.inl (i, true)}

/-- The edge indexed by a spine `i` and an outside vertex `x`. -/
def starEdge {s t : ℕ} (i : Fin s) (x : Fin t) : Hyperedge s t :=
  insert (Sum.inr x) (spinePair i)

/-- The union of the `s` pair-stars. -/
def pairStar (s t : ℕ) : Hypergraph s t :=
  Finset.univ.biUnion fun i : Fin s => Finset.univ.image (starEdge i)

/-- A finite edge family is a matching when distinct edges are disjoint. -/
def IsMatching {s t : ℕ} (M : Finset (Hyperedge s t)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- A Berge triangle consists of three distinct core vertices and three distinct
representing hyperedges, one containing each pair of core vertices. -/
def ContainsBergeTriangle {s t : ℕ} (H : Hypergraph s t) : Prop :=
  ∃ a b c : Vertex s t, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
    ∃ eab ∈ H, ∃ ebc ∈ H, ∃ eca ∈ H,
      eab ≠ ebc ∧ ebc ≠ eca ∧ eca ≠ eab ∧
      a ∈ eab ∧ b ∈ eab ∧ b ∈ ebc ∧ c ∈ ebc ∧ c ∈ eca ∧ a ∈ eca

def BergeTriangleFree {s t : ℕ} (H : Hypergraph s t) : Prop :=
  ¬ ContainsBergeTriangle H

lemma starEdge_injective {s t : ℕ} :
    Function.Injective (fun p : Fin s × Fin t => starEdge p.1 p.2) := by
  intro p q; simp +decide [ starEdge ] ;
  simp +decide [ Finset.ext_iff, spinePair ];
  grind

lemma mem_pairStar_iff {s t : ℕ} {e : Hyperedge s t} :
    e ∈ pairStar s t ↔ ∃ i : Fin s, ∃ x : Fin t, e = starEdge i x := by
  unfold pairStar;
  simp +decide [ eq_comm, Finset.mem_biUnion ]

/-
Every edge in the construction has exactly three vertices.
-/
theorem pairStar_three_uniform {s t : ℕ} {e : Hyperedge s t}
    (he : e ∈ pairStar s t) : e.card = 3 := by
  obtain ⟨ i, x, rfl ⟩ := mem_pairStar_iff.mp he;
  unfold starEdge spinePair; simp +decide [ Finset.card_insert_of_notMem ] ;

/-
Exact edge count of the construction.
-/
theorem card_pairStar (s t : ℕ) : (pairStar s t).card = s * t := by
  rw [ show pairStar s t = Finset.image ( fun p : Fin s × Fin t => starEdge p.fst p.snd ) ( Finset.univ : Finset ( Fin s × Fin t ) ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ starEdge_injective ];
  ext; simp [pairStar]

/-
Distinct edges with the same spine index intersect in their spine pair.
-/
lemma same_spine_not_disjoint {s t : ℕ} (i : Fin s) (x y : Fin t) :
    ¬ Disjoint (starEdge i x) (starEdge i y) := by
  simp +decide [ Finset.disjoint_left, starEdge, spinePair ]

/-
Exact intersection pattern of two construction edges.
-/
theorem card_inter_starEdge {s t : ℕ} (i j : Fin s) (x y : Fin t) :
    (starEdge i x ∩ starEdge j y).card =
      if i = j then (if x = y then 3 else 2) else (if x = y then 1 else 0) := by
  split_ifs <;> simp_all +decide [starEdge, spinePair]

/-- Edges belonging to different pair-stars intersect in at most one vertex. -/
theorem card_inter_le_one_of_ne {s t : ℕ} {i j : Fin s} (hij : i ≠ j)
    (x y : Fin t) : (starEdge i x ∩ starEdge j y).card ≤ 1 := by
  rw [card_inter_starEdge]
  simp [hij]
  split <;> omega

/-
Every matching in the pair-star construction uses each spine at most once.
-/
theorem matching_card_le {s t : ℕ} (M : Finset (Hyperedge s t))
    (hsub : M ⊆ pairStar s t) (hmatch : IsMatching M) : M.card ≤ s := by
  by_contra h_contra;
  obtain ⟨f, hf⟩ : ∃ f : Fin (s + 1) → Hyperedge s t, (∀ i, f i ∈ M) ∧ (∀ i j, i ≠ j → f i ≠ f j) := by
    obtain ⟨f, hf⟩ : ∃ f : Fin (Finset.card M) → Hyperedge s t, (∀ i, f i ∈ M) ∧ (∀ i j, i ≠ j → f i ≠ f j) := by
      have h_inj : Nonempty (Fin (Finset.card M) ≃ M) := by
        exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
      exact ⟨ _, fun i => h_inj.some i |>.2, fun i j hij => fun h => hij <| h_inj.some.injective <| Subtype.ext h ⟩;
    exact ⟨ fun i => f ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i => hf.1 _, fun i j hij => hf.2 _ _ <| by simpa [ Fin.ext_iff ] using hij ⟩;
  obtain ⟨g, hg⟩ : ∃ g : Fin (s + 1) → Fin s, ∀ i, ∃ x : Fin t, f i = starEdge (g i) x := by
    exact ⟨ fun i => Classical.choose ( mem_pairStar_iff.mp ( hsub ( hf.1 i ) ) ), fun i => Classical.choose_spec ( mem_pairStar_iff.mp ( hsub ( hf.1 i ) ) ) ⟩;
  obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin (s + 1), i ≠ j ∧ g i = g j := by
    by_contra! h;
    exact absurd ( Fintype.card_le_of_injective g fun i j hij => not_imp_not.mp ( h i j ) hij ) ( by simp +arith +decide );
  obtain ⟨ x, hx ⟩ := hg i; obtain ⟨ y, hy ⟩ := hg j; specialize hmatch ( f i ) ( hf.1 i ) ( f j ) ( hf.1 j ) ; simp_all +decide [ Finset.disjoint_left ] ;
  grind +locals

/-
If there are at least `s` outside vertices, the construction contains a
matching of size `s`.
-/
theorem exists_matching_card_eq {s t : ℕ} (hst : s ≤ t) :
    ∃ M : Finset (Hyperedge s t), M ⊆ pairStar s t ∧ IsMatching M ∧ M.card = s := by
  refine' ⟨ Finset.image ( fun i : Fin s => starEdge i ⟨ i, lt_of_lt_of_le i.2 hst ⟩ ) Finset.univ, _, _, _ ⟩;
  · exact Finset.image_subset_iff.mpr fun i _ => mem_pairStar_iff.mpr ⟨ i, _, rfl ⟩;
  · intro e he f hf hne; simp_all +decide [ Finset.disjoint_left, starEdge ] ;
    rcases he with ⟨ a, rfl ⟩ ; rcases hf with ⟨ b, rfl ⟩ ; simp_all +decide [ Fin.ext_iff, spinePair ] ;
    grind;
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    simp_all +decide [ Finset.ext_iff, starEdge, spinePair ]

/-
The pair-star construction contains no Berge triangle.
-/
theorem pairStar_bergeTriangleFree (s t : ℕ) :
    BergeTriangleFree (pairStar s t) := by
  intros h; rcases h with ⟨ a, b, c, hab, hbc, hca, eab, heab, ebc, hebc, eca, heca, heab_ne, hebc_ne, heca_ne, ha, hb, hc ⟩ ; simp_all +decide only [mem_pairStar_iff];
  rcases heab with ⟨ i, x, rfl ⟩ ; rcases hebc with ⟨ j, y, rfl ⟩ ; rcases heca with ⟨ k, z, rfl ⟩ ; simp_all +decide [ starEdge, spinePair ] ;
  grind

/-
Main packaged lower-bound result: for `n ≥ 3s`, the construction on
`2s + (n-2s) = n` vertices is 3-uniform, Berge-triangle-free, has matching
number exactly `s`, and has `s(n-2s)` edges.
-/
theorem extremalConstructionData (n s : ℕ) (h : 3 * s ≤ n) :
    (∀ e ∈ pairStar s (n - 2 * s), e.card = 3) ∧
    BergeTriangleFree (pairStar s (n - 2 * s)) ∧
    (∀ M, M ⊆ pairStar s (n - 2 * s) → IsMatching M → M.card ≤ s) ∧
    (∃ M, M ⊆ pairStar s (n - 2 * s) ∧ IsMatching M ∧ M.card = s) ∧
    (pairStar s (n - 2 * s)).card = s * (n - 2 * s) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · grind +locals;
  · exact pairStar_bergeTriangleFree s (n - 2 * s)
  · exact fun M hM hmatch => matching_card_le M hM hmatch
  · exact exists_matching_card_eq ( by omega );
  · convert card_pairStar s ( n - 2 * s ) using 1


/-- The vertex type used by the construction has `2s+t` elements. -/
theorem card_vertex (s t : ℕ) : Fintype.card (Vertex s t) = 2 * s + t := by
  simp [Vertex]
  omega

/-- Under the paper's range hypothesis, the extremal construction really is an
`n`-vertex hypergraph (not merely one with the desired edge count). -/
theorem card_vertex_extremal (n s : ℕ) (h : 3 * s ≤ n) :
    Fintype.card (Vertex s (n - 2 * s)) = n := by
  rw [card_vertex]
  omega

end HypergraphTuran


