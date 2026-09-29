-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.not_macajovaSkoviera_of_bridge_with_finite_side
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:59:22.056842+00:00
-- url     : https://prove2.me/submissions/157fd4f2-8603-4843-9312-b56f3af23eea

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridgeParity

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Bridges/InfiniteCubicMatchings.lean ====
/-
# Perfect matching conjectures in (possibly infinite) cubic bridgeless graphs

This file develops a formal framework, valid for **arbitrary** (finite or infinite) vertex
types, for the three classical perfect-matching conjectures on cubic bridgeless graphs:

* the **Berge–Fulkerson conjecture** (`BergeFulkerson`): six perfect matchings covering
  every edge exactly twice;
* the **Fan–Raspaud conjecture** (`FanRaspaud`): three perfect matchings with empty
  intersection;
* the **Máčajová–Škoviera conjecture** (`MacajovaSkoviera`): two perfect matchings whose
  intersection contains no odd edge cut.

The main results proved here are

* `PerfectMatching.exists_mem_cutEdges` and `PerfectMatching.card_inter_cutEdges_odd`:
  the *parity lemma* in the infinite setting — a perfect matching meets every edge cut with
  a **finite odd side** in an odd (in particular nonzero) number of edges;
* `BergeFulkerson.fanRaspaud` : BF ⟹ FR;
* `FanRaspaud.macajovaSkoviera` : FR ⟹ MŠ (this is where the parity lemma is used);
* `BergeFulkerson.macajovaSkoviera` : BF ⟹ MŠ;
* `not_bergeFulkerson_of_oddCut_singleton` and friends: all three conjectures **fail** for a
  graph possessing a one-edge cut with a finite odd side (the infinite analogue of "a cubic
  graph with a bridge has no such family"); hence bridgelessness is a necessary hypothesis;
* `ProperThreeEdgeColoring.bergeFulkerson` : a 3-edge-colourable graph satisfies BF (by
  doubling the colour classes) — this works verbatim for infinite graphs;
* transport of all three properties along graph isomorphisms.

Everything is stated for an arbitrary vertex type `V`; no finiteness of `V` is assumed
anywhere.
-/

namespace Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-! ## Perfect matchings as fixed-point-free involutions -/

-- [dropped: platform already declares PerfectMatching]
namespace PerfectMatching

-- [dropped: platform already declares edges]
@[simp] lemma mem_edges (M : PerfectMatching G) (u w : V) :
    s(u, w) ∈ M.edges ↔ M.partner u = w := by
  constructor
  · rintro ⟨x, hx⟩
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact M.invol _
  · rintro rfl
    exact ⟨u, rfl⟩

lemma edges_subset_edgeSet (M : PerfectMatching G) : M.edges ⊆ G.edgeSet := by
  rintro e ⟨v, rfl⟩
  simpa using M.isAdj v

lemma partner_ne (M : PerfectMatching G) (v : V) : M.partner v ≠ v :=
  fun h => G.irrefl (h ▸ M.isAdj v)

/-- Two perfect matchings that never share a partner have disjoint edge sets. -/
lemma disjoint_edges (M N : PerfectMatching G) (h : ∀ v, M.partner v ≠ N.partner v) :
    Disjoint M.edges N.edges := by
  rw [Set.disjoint_left]
  intro e
  induction e with
  | _ u w =>
    intro h1 h2
    rw [mem_edges] at h1 h2
    exact h u (h1.trans h2.symm)

/-- The subgraph associated with a perfect matching. -/
-- [dropped: platform already declares toSubgraph]
theorem toSubgraph_isPerfectMatching (M : PerfectMatching G) :
    M.toSubgraph.IsPerfectMatching := by
  constructor
  · intro v _
    refine ⟨M.partner v, ⟨M.isAdj v, rfl⟩, ?_⟩
    rintro w ⟨-, rfl⟩
    rfl
  · intro v; exact Set.mem_univ v

end PerfectMatching

/-! ## Edge cuts with a finite side -/

-- [dropped: platform already declares cutEdges]
lemma cutEdges_subset_edgeSet (S : Finset V) : cutEdges G S ⊆ G.edgeSet := fun _ h => h.1

/-- The edge cut of an arbitrary, possibly infinite, set of vertices. -/
-- [dropped: platform already declares cutEdgesSet]
lemma cutEdges_eq_cutEdgesSet (S : Finset V) : cutEdges G S = cutEdgesSet G ↑S := rfl

/-- An *odd cut* (with a finite side): the cut of a finite vertex set of odd cardinality.
In an infinite graph, cuts both of whose sides are infinite carry no parity information,
so this finiteness restriction is essential. -/
-- [dropped: platform already declares IsOddCut]
theorem even_card_of_involutive {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α)
    (hmaps : ∀ a ∈ s, f a ∈ s) (hinv : ∀ a ∈ s, f (f a) = a) (hne : ∀ a ∈ s, f a ≠ a) :
    Even s.card := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  subst hn
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
  · simp
  · have hfa : f a ∈ s := hmaps a ha
    have hane : f a ≠ a := hne a ha
    set t : Finset α := s \ {a, f a} with ht
    have hsub : ({a, f a} : Finset α) ⊆ s := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair : ({a, f a} : Finset α).card = 2 := Finset.card_pair (Ne.symm hane)
    have hcardt : t.card = s.card - 2 := by
      rw [ht, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hpair]
    have h2 : 2 ≤ s.card := by
      have := Finset.card_le_card hsub
      rw [hpair] at this
      exact this
    have hmaps' : ∀ b ∈ t, f b ∈ t := by
      intro b hb
      rw [ht, Finset.mem_sdiff] at hb ⊢
      obtain ⟨hbs, hbn⟩ := hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbn ⊢
      refine ⟨hmaps b hbs, ?_, ?_⟩
      · intro h
        exact hbn.2 (by rw [← h, hinv b hbs])
      · intro h
        exact hbn.1 (by
          have := congrArg f h
          rwa [hinv b hbs, hinv a ha] at this)
    have hinv' : ∀ b ∈ t, f (f b) = b := fun b hb => hinv b (Finset.mem_sdiff.mp hb).1
    have hne' : ∀ b ∈ t, f b ≠ b := fun b hb => hne b (Finset.mem_sdiff.mp hb).1
    obtain ⟨m, hm⟩ := ih t.card (by omega) t hmaps' hinv' hne' rfl
    exact ⟨m + 1, by omega⟩

/-! ## The parity lemma -/

namespace PerfectMatching

variable (M : PerfectMatching G)

open scoped Classical in
/-- The edges of `M` crossing the cut of `S` are exactly the edges `s(v, partner v)` for
`v ∈ S` with `partner v ∉ S`. -/
theorem inter_cutEdges_eq (S : Finset V) :
    M.edges ∩ cutEdges G S =
      ↑((S.filter (fun v => M.partner v ∉ S)).image (fun v => s(v, M.partner v))) := by
  ext e
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨hM, -, u, w, rfl, huS, hwS⟩
    rw [mem_edges] at hM
    subst hM
    exact ⟨u, ⟨huS, hwS⟩, rfl⟩
  · rintro ⟨v, ⟨hvS, hpv⟩, rfl⟩
    refine ⟨⟨v, rfl⟩, ?_, v, M.partner v, rfl, hvS, hpv⟩
    simpa using M.isAdj v

/-- **Parity lemma** (infinite version).  If `S` is a finite set of vertices with an odd
number of elements, then every perfect matching contains an odd number of edges of the cut
`cutEdges G S`.  (The intersection is automatically finite.) -/
theorem card_inter_cutEdges_odd (S : Finset V) (hS : Odd S.card) :
    Odd (M.edges ∩ cutEdges G S).ncard := by
  classical
  have hinj : Set.InjOn (fun v => s(v, M.partner v))
      ↑(S.filter (fun v => M.partner v ∉ S)) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rfl
    · exact absurd hb.1 (by simpa [M.invol] using ha.2)
  rw [inter_cutEdges_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn (by
    simpa using hinj)]
  -- the complementary part of `S` is even, being stable under the partner involution
  have hEven : Even (S.filter (fun v => M.partner v ∈ S)).card := by
    refine even_card_of_involutive _ M.partner ?_ (fun a _ => M.invol a)
      (fun a _ => M.partner_ne a)
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.2, by rw [M.invol]; exact ha.1⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun v => M.partner v ∈ S)
  rcases hS with ⟨k, hk⟩
  rcases hEven with ⟨m, hm⟩
  refine ⟨k - m, ?_⟩
  omega

/-- A perfect matching meets every odd cut. -/
theorem exists_mem_cutEdges (S : Finset V) (hS : Odd S.card) :
    (M.edges ∩ cutEdges G S).Nonempty := by
  have h := M.card_inter_cutEdges_odd S hS
  rw [Set.nonempty_iff_ne_empty]
  rintro he
  rw [he] at h
  simp at h

/-- A perfect matching meets every odd cut. -/
theorem exists_mem_of_isOddCut {C : Set (Sym2 V)} (hC : IsOddCut G C) :
    (M.edges ∩ C).Nonempty := by
  obtain ⟨S, hS, rfl⟩ := hC
  exact M.exists_mem_cutEdges S hS

end PerfectMatching

/-! ## The three conjectures -/

-- [dropped: platform already declares BergeFulkerson]
-- [dropped: platform already declares FanRaspaud]
-- [dropped: platform already declares MacajovaSkoviera]
-- [dropped: platform already declares ProperThreeEdgeColoring]
-- [dropped: platform already declares IsCubic]
-- [dropped: platform already declares Bridgeless]
theorem BergeFulkerson.fanRaspaud (h : BergeFulkerson G) : FanRaspaud G := by
  obtain ⟨M, hM⟩ := h
  refine ⟨![M 0, M 1, M 2], ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro e ⟨⟨h0, h1⟩, h2⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  have hE : e ∈ G.edgeSet := (M 0).edges_subset_edgeSet h0
  have hsub : ({0, 1, 2} : Set (Fin 6)) ⊆ {i : Fin 6 | e ∈ (M i).edges} := by
    rintro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have hcard : ({0, 1, 2} : Set (Fin 6)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by decide) (Set.toFinite _),
      Set.ncard_insert_of_notMem (by decide) (Set.toFinite _), Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, hM e hE] at this
  omega

theorem FanRaspaud.macajovaSkoviera (h : FanRaspaud G) : MacajovaSkoviera G := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M 0, M 1, ?_⟩
  intro C hC hsub
  obtain ⟨e, he2, heC⟩ := (M 2).exists_mem_of_isOddCut hC
  obtain ⟨he0, he1⟩ := hsub heC
  have : e ∈ (M 0).edges ∩ (M 1).edges ∩ (M 2).edges := ⟨⟨he0, he1⟩, he2⟩
  rw [hM] at this
  exact this

theorem BergeFulkerson.macajovaSkoviera (h : BergeFulkerson G) : MacajovaSkoviera G :=
  h.fanRaspaud.macajovaSkoviera

/-! ## Bridgelessness is necessary: one-edge odd cuts destroy all three properties -/

/-- Every perfect matching contains an edge forming a one-edge odd cut (the infinite
analogue of "every perfect matching contains every bridge"). -/
theorem mem_edges_of_isOddCut_singleton (M : PerfectMatching G) {e : Sym2 V}
    (h : IsOddCut G {e}) : e ∈ M.edges := by
  obtain ⟨f, hf, hfe⟩ := M.exists_mem_of_isOddCut h
  rwa [Set.mem_singleton_iff.mp hfe] at hf

theorem edge_mem_edgeSet_of_isOddCut_singleton {e : Sym2 V} (h : IsOddCut G {e}) :
    e ∈ G.edgeSet := by
  obtain ⟨S, -, hS⟩ := h
  exact cutEdges_subset_edgeSet S (hS ▸ rfl)

theorem not_bergeFulkerson_of_oddCut_singleton {e : Sym2 V} (h : IsOddCut G {e}) :
    ¬ BergeFulkerson G := by
  rintro ⟨M, hM⟩
  have hE : e ∈ G.edgeSet := edge_mem_edgeSet_of_isOddCut_singleton h
  have huniv : {i : Fin 6 | e ∈ (M i).edges} = Set.univ := by
    ext i
    simp [mem_edges_of_isOddCut_singleton (M i) h]
  have := hM e hE
  rw [huniv, Set.ncard_univ] at this
  simp at this

theorem not_fanRaspaud_of_oddCut_singleton {e : Sym2 V} (h : IsOddCut G {e}) :
    ¬ FanRaspaud G := by
  rintro ⟨M, hM⟩
  have : e ∈ (M 0).edges ∩ (M 1).edges ∩ (M 2).edges :=
    ⟨⟨mem_edges_of_isOddCut_singleton _ h, mem_edges_of_isOddCut_singleton _ h⟩,
      mem_edges_of_isOddCut_singleton _ h⟩
  rw [hM] at this
  exact this

theorem not_macajovaSkoviera_of_oddCut_singleton {e : Sym2 V} (h : IsOddCut G {e}) :
    ¬ MacajovaSkoviera G := by
  rintro ⟨M₁, M₂, hM⟩
  refine hM {e} h ?_
  rintro f hf
  rw [Set.mem_singleton_iff.mp hf]
  exact ⟨mem_edges_of_isOddCut_singleton _ h, mem_edges_of_isOddCut_singleton _ h⟩

/-! ## 3-edge-colourable graphs satisfy Berge–Fulkerson -/

theorem ProperThreeEdgeColoring.bergeFulkerson (h : ProperThreeEdgeColoring G) :
    BergeFulkerson G := by
  obtain ⟨M, hdisj, hcover⟩ := h
  refine ⟨fun i => M ⟨i.1 / 2, by omega⟩, ?_⟩
  intro e hE
  obtain ⟨i₀, hi₀⟩ := hcover e hE
  have key : {i : Fin 6 | e ∈ (M ⟨i.1 / 2, by omega⟩).edges} = {i : Fin 6 | i.1 / 2 = i₀.1} := by
    ext i
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hi
      by_contra hne
      have : (⟨i.1 / 2, by omega⟩ : Fin 3) ≠ i₀ := by
        intro hEq
        exact hne (congrArg Fin.val hEq)
      exact (hdisj _ _ this).le_bot ⟨hi, hi₀⟩
    · intro hi
      have : (⟨i.1 / 2, by omega⟩ : Fin 3) = i₀ := Fin.ext hi
      rw [this]
      exact hi₀
  rw [key]
  have hc : ∀ j : Fin 3, {i : Fin 6 | i.1 / 2 = j.1}.ncard = 2 := by
    intro j
    simp only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    revert j
    decide
  exact hc i₀

/-! ## Invariance under isomorphism -/

namespace PerfectMatching

variable {W : Type v} {H : SimpleGraph W}

-- [dropped: platform already declares map]
@[simp] lemma mem_map_edges (f : G ≃g H) (M : PerfectMatching G) (u w : V) :
    s(f u, f w) ∈ (M.map f).edges ↔ s(u, w) ∈ M.edges := by
  simp only [mem_edges, map]
  constructor
  · intro h
    have := congrArg f.symm h
    simpa using this
  · intro h
    rw [show f.symm (f u) = u by simp, h]

lemma mem_map_edges' (f : G ≃g H) (M : PerfectMatching G) (e : Sym2 W) :
    e ∈ (M.map f).edges ↔ Sym2.map f.symm e ∈ M.edges := by
  induction e with
  | _ a b =>
    rw [Sym2.map_pair_eq, show s(a, b) = s(f (f.symm a), f (f.symm b)) by simp]
    exact mem_map_edges f M _ _

end PerfectMatching

lemma mem_edgeSet_map_symm {W : Type v} {H : SimpleGraph W} (f : G ≃g H) (e : Sym2 W) :
    Sym2.map f.symm e ∈ G.edgeSet ↔ e ∈ H.edgeSet := by
  induction e with
  | _ a b =>
    simp only [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
    exact f.symm.map_adj_iff

/-- The image of a cut edge under an isomorphism matching the two sides is a cut edge. -/
lemma mem_cutEdges_map {W : Type v} {H : SimpleGraph W} (f : G ≃g H) (S : Finset V)
    (T : Finset W) (hST : ∀ v : V, v ∈ S ↔ f v ∈ T) {e : Sym2 V} (he : e ∈ cutEdges G S) :
    Sym2.map f e ∈ cutEdges H T := by
  obtain ⟨heE, u, w, rfl, huS, hwS⟩ := he
  refine ⟨?_, f u, f w, by simp, (hST u).mp huS, fun hc => hwS ((hST w).mpr hc)⟩
  simpa using f.map_adj_iff.mpr (by simpa using heE)

/-- The Berge–Fulkerson property is invariant under graph isomorphism. -/
theorem BergeFulkerson.map {W : Type v} {H : SimpleGraph W} (f : G ≃g H)
    (h : BergeFulkerson G) : BergeFulkerson H := by
  obtain ⟨M, hM⟩ := h
  refine ⟨fun i => (M i).map f, fun e hE => ?_⟩
  have key : {i : Fin 6 | e ∈ ((M i).map f).edges}
      = {i : Fin 6 | Sym2.map f.symm e ∈ (M i).edges} := by
    ext i
    exact PerfectMatching.mem_map_edges' f (M i) e
  rw [key]
  exact hM _ ((mem_edgeSet_map_symm f e).mpr hE)

/-- The Fan–Raspaud property is invariant under graph isomorphism. -/
theorem FanRaspaud.map {W : Type v} {H : SimpleGraph W} (f : G ≃g H)
    (h : FanRaspaud G) : FanRaspaud H := by
  obtain ⟨M, hM⟩ := h
  refine ⟨fun i => (M i).map f, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro e ⟨⟨h0, h1⟩, h2⟩
  rw [PerfectMatching.mem_map_edges'] at h0 h1 h2
  have : Sym2.map f.symm e ∈ (M 0).edges ∩ (M 1).edges ∩ (M 2).edges := ⟨⟨h0, h1⟩, h2⟩
  rw [hM] at this
  exact this

/-- The Máčajová–Škoviera property is invariant under graph isomorphism. -/
theorem MacajovaSkoviera.map {W : Type v} {H : SimpleGraph W} (f : G ≃g H)
    (h : MacajovaSkoviera G) : MacajovaSkoviera H := by
  classical
  obtain ⟨M₁, M₂, hM⟩ := h
  refine ⟨M₁.map f, M₂.map f, ?_⟩
  rintro C ⟨T, hT, rfl⟩ hsub
  refine hM (cutEdges G (T.image f.symm)) ⟨T.image f.symm, ?_, rfl⟩ ?_
  · rwa [Finset.card_image_of_injective _ f.symm.injective]
  · intro e he
    have hST : ∀ v : V, v ∈ T.image f.symm ↔ f v ∈ T := by
      intro v
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hv; exact ⟨f v, hv, by simp⟩
    have hmap := mem_cutEdges_map f _ T hST he
    obtain ⟨h1, h2⟩ := hsub hmap
    rw [PerfectMatching.mem_map_edges'] at h1 h2
    simp only [Sym2.map_map, Function.comp, RelIso.symm_apply_apply, Sym2.map_id'] at h1 h2
    exact ⟨h1, h2⟩

end Bridges.InfiniteCubicMatchings
-- ==== upstream: Packages/Catalog/Bridges/InfiniteCubicMatchingsBridgeParity.lean ====
/-
# Cut parity in cubic graphs, and bridges versus finite sides

`InfiniteCubicMatchings.lean` proves that a graph possessing a **one-edge odd cut** satisfies
none of the three properties (`not_bergeFulkerson_of_oddCut_singleton` and friends), where
`IsOddCut G {e}` asks for a finite vertex set `S` of *odd* cardinality with
`cutEdges G S = {e}`.  In the finite world one never checks that parity by hand: a cubic graph
with a bridge automatically has an odd side, by the handshake lemma.  In the infinite world the
argument has to be redone for a *finite side of a possibly infinite graph*, and doing so was
next-cycle sub-conjecture 3 of `FUTURE_DIRECTIONS.md`.

This file proves it, in the sharpest form available.  The engine is
`cutEdges_finite_and_handshake`: for a cubic graph and **any** finite vertex set `S`, the cut
`cutEdges G S` is finite and

  `3 * S.card = 2 * m + (cutEdges G S).ncard`   for some `m`,

by a half-edge count — the set of pairs `(v, w)` with `v ∈ S` and `v` adjacent to `w` has
exactly `3 * S.card` elements; the pairs with `w ∈ S` form a set stable under a fixed-point-free
involution (swap), hence of even size; and the pairs with `w ∉ S` are in bijection with the cut.
Consequently `S.card` and `(cutEdges G S).ncard` always have the *same parity*
(`odd_card_iff_odd_ncard_cutEdges`), which is the infinite-graph form of the classical
"odd side ⟺ odd cut" for cubic graphs.

Consequences:

* `isOddCut_iff_odd_ncard` : for a cubic graph, `C` is an odd cut in the sense of `IsOddCut`
  iff it is the cut of some finite vertex set and has an odd number of edges;
* `isOddCut_singleton_iff` : in particular the parity hypothesis is automatic for one-edge
  cuts, so the obstruction in `not_bergeFulkerson_of_oddCut_singleton` is exactly
  "a one-edge cut with a finite side";
* `cutEdgesSet_bridgeSide` : the vertex set reachable from `u` after deleting a bridge
  `s(u, w)` has exactly `{s(u, w)}` as its cut;
* `not_bergeFulkerson_of_bridge_with_finite_side` (and the `FanRaspaud` / `MacajovaSkoviera`
  versions) : a cubic graph with a bridge one of whose sides is finite satisfies none of the
  three properties;
* `bridge_sides_infinite_of_bergeFulkerson` : hence, in a cubic graph satisfying
  Berge–Fulkerson, **every bridge separates two infinite sides**.  Together with
  `exists_bridged_cubic_bergeFulkerson` of `…Bridged.lean` this is sharp; the two halves are
  combined in `…BridgeSharp.lean`.
-/

namespace Bridges.InfiniteCubicMatchings

universe u

variable {V : Type u} {G : SimpleGraph V}

/-! ## The half-edge count -/

/-- In a cubic graph every neighbour set is finite (an infinite set has `ncard = 0`). -/
lemma IsCubic.neighborSet_finite (hG : IsCubic G) (v : V) : (G.neighborSet v).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [hG v]; omega)

/-- **The handshake lemma for a finite side of a cubic graph.**  For every finite vertex set
`S` of a cubic graph the edge cut of `S` is finite and `3 * S.card` exceeds its size by an even
number.  No finiteness of `V`, and no bridgelessness, is assumed. -/
theorem cutEdges_finite_and_handshake (hG : IsCubic G) (S : Finset V) :
    (cutEdges G S).Finite ∧ ∃ m : ℕ, 3 * S.card = 2 * m + (cutEdges G S).ncard := by
  classical
  have hfin : ∀ v : V, (G.neighborSet v).Finite := hG.neighborSet_finite
  -- the neighbours of `v`, as a `Finset`
  set N : V → Finset V := fun v => (hfin v).toFinset with hNdef
  have hNmem : ∀ v w : V, w ∈ N v ↔ G.Adj v w := by
    intro v w
    simp [hNdef]
  have hNcard : ∀ v, (N v).card = 3 := by
    intro v
    have h3 := hG v
    rwa [Set.ncard_eq_toFinset_card _ (hfin v)] at h3
  -- the half-edges based in `S`
  set D : Finset (V × V) := S.biUnion (fun v => (N v).image (fun w => (v, w))) with hDdef
  have hDmem : ∀ p : V × V, p ∈ D ↔ p.1 ∈ S ∧ G.Adj p.1 p.2 := by
    rintro ⟨a, b⟩
    constructor
    · intro hp
      rw [hDdef, Finset.mem_biUnion] at hp
      obtain ⟨v, hvS, hv⟩ := hp
      rw [Finset.mem_image] at hv
      obtain ⟨w, hw, hvw⟩ := hv
      cases hvw
      exact ⟨hvS, (hNmem _ _).mp hw⟩
    · rintro ⟨haS, hab⟩
      rw [hDdef, Finset.mem_biUnion]
      exact ⟨a, haS, Finset.mem_image.mpr ⟨b, (hNmem _ _).mpr hab, rfl⟩⟩
  have hDcard : D.card = 3 * S.card := by
    rw [hDdef, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun v _ => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.card_image_of_injective _ (fun x y hxy => (Prod.mk.injEq _ _ _ _ ▸ hxy).2),
        hNcard v]
    · intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨wx, -, hax⟩ := hx
      obtain ⟨wy, -, hay⟩ := hy
      rw [Prod.mk.injEq] at hax hay
      exact hxy (hax.1.trans hay.1.symm)
  -- split into inner and outgoing half-edges
  have hsplit : (D.filter fun p => p.2 ∈ S).card + (D.filter fun p => p.2 ∉ S).card = D.card :=
    Finset.card_filter_add_card_filter_not _
  -- the inner half-edges are permuted by `swap`, a fixed-point-free involution, so there is an
  -- even number of them
  have hinner : Even (D.filter fun p => p.2 ∈ S).card := by
    refine even_card_of_involutive _ Prod.swap ?_ (fun a _ => Prod.swap_swap a) ?_
    · rintro ⟨a, b⟩ hp
      rw [Finset.mem_filter, hDmem] at hp
      obtain ⟨⟨haS, hab⟩, hbS⟩ := hp
      rw [Finset.mem_filter, hDmem]
      exact ⟨⟨hbS, hab.symm⟩, haS⟩
    · rintro ⟨a, b⟩ hp
      rw [Finset.mem_filter, hDmem] at hp
      intro hcon
      exact hp.1.2.ne (congrArg Prod.fst hcon).symm
  -- the outgoing half-edges are in bijection with the cut
  set E : Finset (Sym2 V) := (D.filter fun p => p.2 ∉ S).image (fun p => s(p.1, p.2)) with hEdef
  have hEcoe : (↑E : Set (Sym2 V)) = cutEdges G S := by
    ext f
    constructor
    · intro hf
      rw [Finset.mem_coe, hEdef, Finset.mem_image] at hf
      obtain ⟨p, hp, rfl⟩ := hf
      rw [Finset.mem_filter, hDmem] at hp
      exact ⟨hp.1.2, p.1, p.2, rfl, hp.1.1, hp.2⟩
    · rintro ⟨hfE, a, b, rfl, haS, hbS⟩
      rw [Finset.mem_coe, hEdef, Finset.mem_image]
      exact ⟨(a, b), by rw [Finset.mem_filter, hDmem]; exact ⟨⟨haS, hfE⟩, hbS⟩, rfl⟩
  have hEcard : E.card = (D.filter fun p => p.2 ∉ S).card := by
    rw [hEdef]
    refine Finset.card_image_of_injOn ?_
    rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hpq
    rw [Finset.mem_coe, Finset.mem_filter, hDmem] at hp hq
    rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Prod.mk.injEq]
      exact ⟨h1, h2⟩
    · exact absurd (h1 ▸ hp.1.1) hq.2
  have hncard : (cutEdges G S).ncard = (D.filter fun p => p.2 ∉ S).card := by
    rw [← hEcoe, Set.ncard_coe_finset, hEcard]
  refine ⟨hEcoe ▸ E.finite_toSet, ?_⟩
  obtain ⟨m, hm⟩ := hinner
  refine ⟨m, ?_⟩
  rw [hncard]
  omega

/-- Cuts of finite vertex sets in a cubic graph are finite. -/
theorem cutEdges_finite (hG : IsCubic G) (S : Finset V) : (cutEdges G S).Finite :=
  (cutEdges_finite_and_handshake hG S).1

/-- **Cut parity.**  In a cubic graph a finite vertex set has odd cardinality exactly when its
edge cut has an odd number of edges. -/
theorem odd_card_iff_odd_ncard_cutEdges (hG : IsCubic G) (S : Finset V) :
    Odd S.card ↔ Odd (cutEdges G S).ncard := by
  obtain ⟨-, m, hm⟩ := cutEdges_finite_and_handshake hG S
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-- **Odd cuts are exactly the cuts with an odd number of edges.**  For a cubic graph, the
definition of `IsOddCut` (an odd *vertex set* with a finite side) is equivalent to the usual
"the cut has odd size", so no parity bookkeeping on the vertex side is ever needed. -/
theorem isOddCut_iff_odd_ncard (hG : IsCubic G) (C : Set (Sym2 V)) :
    IsOddCut G C ↔ ∃ S : Finset V, C = cutEdges G S ∧ Odd C.ncard := by
  constructor
  · rintro ⟨S, hSodd, rfl⟩
    exact ⟨S, rfl, (odd_card_iff_odd_ncard_cutEdges hG S).mp hSodd⟩
  · rintro ⟨S, rfl, hodd⟩
    exact ⟨S, (odd_card_iff_odd_ncard_cutEdges hG S).mpr hodd, rfl⟩

/-- **The Máčajová–Škoviera property in edge terms.**  For a cubic graph the condition can be
stated entirely in terms of the *number of edges* of a cut, with no reference to the parity of
the vertex side: two perfect matchings work iff no cut with an odd number of edges (and a
finite side) is contained in their intersection.  This is the form in which the conjecture is
usually stated for finite graphs. -/
theorem macajovaSkoviera_iff_of_isCubic (hG : IsCubic G) :
    MacajovaSkoviera G ↔ ∃ M₁ M₂ : PerfectMatching G,
      ∀ S : Finset V, Odd (cutEdges G S).ncard → ¬ cutEdges G S ⊆ M₁.edges ∩ M₂.edges := by
  constructor
  · rintro ⟨M₁, M₂, h⟩
    exact ⟨M₁, M₂, fun S hS =>
      h _ ⟨S, (odd_card_iff_odd_ncard_cutEdges hG S).mpr hS, rfl⟩⟩
  · rintro ⟨M₁, M₂, h⟩
    refine ⟨M₁, M₂, ?_⟩
    rintro C ⟨S, hSodd, rfl⟩
    exact h S ((odd_card_iff_odd_ncard_cutEdges hG S).mp hSodd)

/-- **Handshake for a finite side.**  In a cubic graph, a finite vertex set whose edge cut is a
single edge has odd cardinality. -/
theorem odd_card_of_cutEdges_eq_singleton (hG : IsCubic G) (S : Finset V) {e : Sym2 V}
    (h : cutEdges G S = {e}) : Odd S.card :=
  (odd_card_iff_odd_ncard_cutEdges hG S).mpr (by rw [h, Set.ncard_singleton]; exact odd_one)

/-- **Exact characterisation of one-edge odd cuts in a cubic graph.**  The parity requirement
in `IsOddCut` is automatic for one-edge cuts: `{e}` is an odd cut iff it is the cut of some
finite vertex set at all. -/
theorem isOddCut_singleton_iff (hG : IsCubic G) (e : Sym2 V) :
    IsOddCut G {e} ↔ ∃ S : Finset V, cutEdges G S = {e} := by
  constructor
  · rintro ⟨S, -, hS⟩
    exact ⟨S, hS.symm⟩
  · rintro ⟨S, hS⟩
    exact ⟨S, odd_card_of_cutEdges_eq_singleton hG S hS, hS.symm⟩

/-! ## Bridges -/

/-- The set of vertices still reachable from `u` after deleting the edge `s(u, w)`. -/
-- [dropped: platform already declares bridgeSide]
theorem cutEdgesSet_bridgeSide {u w : V} (h : G.IsBridge s(u, w)) :
    cutEdgesSet G (bridgeSide G u w) = {s(u, w)} := by
  rw [SimpleGraph.isBridge_iff] at h
  obtain ⟨hadj, hnr⟩ := h
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨hadj, u, w, rfl, SimpleGraph.Reachable.refl u, hnr⟩, ?_⟩
  rintro f ⟨hfE, a, b, rfl, haS, hbS⟩
  by_contra hne
  -- if `s(a, b)` is not the deleted edge it survives the deletion, so `b` is on `u`'s side
  have hadj' : (G \ SimpleGraph.fromEdgeSet {s(u, w)}).Adj a b := by
    refine ⟨hfE, ?_⟩
    rintro ⟨hmem, -⟩
    exact hne (Set.mem_singleton_iff.mp hmem)
  exact hbS (haS.trans hadj'.reachable)

/-- A cubic graph with a bridge one of whose sides is finite has a one-edge odd cut. -/
theorem isOddCut_singleton_of_bridge_finite_side (hG : IsCubic G) {u w : V}
    (hbr : G.IsBridge s(u, w)) (hfin : (bridgeSide G u w).Finite) :
    IsOddCut G {s(u, w)} := by
  have hcut : cutEdges G hfin.toFinset = {s(u, w)} := by
    rw [cutEdges_eq_cutEdgesSet, hfin.coe_toFinset]
    exact cutEdgesSet_bridgeSide hbr
  exact (isOddCut_singleton_iff hG _).mpr ⟨hfin.toFinset, hcut⟩

theorem not_bergeFulkerson_of_bridge_with_finite_side (hG : IsCubic G) {u w : V}
    (hbr : G.IsBridge s(u, w)) (hfin : (bridgeSide G u w).Finite) : ¬ BergeFulkerson G :=
  not_bergeFulkerson_of_oddCut_singleton (isOddCut_singleton_of_bridge_finite_side hG hbr hfin)

theorem not_fanRaspaud_of_bridge_with_finite_side (hG : IsCubic G) {u w : V}
    (hbr : G.IsBridge s(u, w)) (hfin : (bridgeSide G u w).Finite) : ¬ FanRaspaud G :=
  not_fanRaspaud_of_oddCut_singleton (isOddCut_singleton_of_bridge_finite_side hG hbr hfin)

theorem not_macajovaSkoviera_of_bridge_with_finite_side (hG : IsCubic G) {u w : V}
    (hbr : G.IsBridge s(u, w)) (hfin : (bridgeSide G u w).Finite) : ¬ MacajovaSkoviera G :=
  not_macajovaSkoviera_of_oddCut_singleton
    (isOddCut_singleton_of_bridge_finite_side hG hbr hfin)

/-- **Every bridge of a cubic graph satisfying Máčajová–Škoviera separates two infinite
sides.**  (Since `BergeFulkerson → FanRaspaud → MacajovaSkoviera`, the same holds under either
of the two stronger hypotheses; see the corollaries below.)  This is sharp: `k4Chain` of
`…Bridged.lean` is an infinite cubic graph with infinitely many bridges — all of them with two
infinite sides — that satisfies all three properties. -/
theorem bridge_sides_infinite_of_macajovaSkoviera (hG : IsCubic G) (hMS : MacajovaSkoviera G)
    {u w : V} (hbr : G.IsBridge s(u, w)) :
    (bridgeSide G u w).Infinite ∧ (bridgeSide G w u).Infinite := by
  have hbr' : G.IsBridge s(w, u) := by rwa [Sym2.eq_swap] at hbr
  exact ⟨fun hfin => not_macajovaSkoviera_of_bridge_with_finite_side hG hbr hfin hMS,
    fun hfin => not_macajovaSkoviera_of_bridge_with_finite_side hG hbr' hfin hMS⟩

theorem bridge_sides_infinite_of_fanRaspaud (hG : IsCubic G) (hFR : FanRaspaud G)
    {u w : V} (hbr : G.IsBridge s(u, w)) :
    (bridgeSide G u w).Infinite ∧ (bridgeSide G w u).Infinite :=
  bridge_sides_infinite_of_macajovaSkoviera hG hFR.macajovaSkoviera hbr

theorem bridge_sides_infinite_of_bergeFulkerson (hG : IsCubic G) (hBF : BergeFulkerson G)
    {u w : V} (hbr : G.IsBridge s(u, w)) :
    (bridgeSide G u w).Infinite ∧ (bridgeSide G w u).Infinite :=
  bridge_sides_infinite_of_macajovaSkoviera hG hBF.macajovaSkoviera hbr

/-- In particular, a cubic graph satisfying Máčajová–Škoviera has an infinite vertex set as
soon as it has a bridge at all: bridgelessness can only fail infinitely. -/
theorem infinite_of_macajovaSkoviera_of_bridge (hG : IsCubic G) (hMS : MacajovaSkoviera G)
    {u w : V} (hbr : G.IsBridge s(u, w)) : Infinite V := by
  have h := (bridge_sides_infinite_of_macajovaSkoviera hG hMS hbr).1
  have : Infinite (bridgeSide G u w) := h.to_subtype
  exact Infinite.of_injective (Subtype.val : bridgeSide G u w → V) Subtype.val_injective

/-- The finite case of the classical statement, recovered: a **finite** cubic graph with a
bridge satisfies none of the three properties.  (Bridgelessness really is necessary in the
finite setting, while `…Bridged.lean` shows that it is not in the infinite one.) -/
theorem not_bergeFulkerson_of_bridge_of_finite [Finite V] (hG : IsCubic G) {u w : V}
    (hbr : G.IsBridge s(u, w)) : ¬ BergeFulkerson G :=
  not_bergeFulkerson_of_bridge_with_finite_side hG hbr (Set.toFinite _)

end Bridges.InfiniteCubicMatchings
section
universe u
open Bridges.InfiniteCubicMatchings
variable {V : Type u} {G : SimpleGraph V}

theorem solution (hG : IsCubic G) {u w : V}
    (hbr : G.IsBridge s(u, w)) (hfin : (bridgeSide G u w).Finite) :
    ¬ MacajovaSkoviera G := by
  first
  | exact Bridges.InfiniteCubicMatchings.not_macajovaSkoviera_of_bridge_with_finite_side hG hbr hfin
  | exact Bridges.InfiniteCubicMatchings.not_macajovaSkoviera_of_bridge_with_finite_side
  | exact @Bridges.InfiniteCubicMatchings.not_macajovaSkoviera_of_bridge_with_finite_side hG u w hbr hfin
  | apply Bridges.InfiniteCubicMatchings.not_macajovaSkoviera_of_bridge_with_finite_side
  | exact Bridges.InfiniteCubicMatchings.not_macajovaSkoviera_of_bridge_with_finite_side ..


end
