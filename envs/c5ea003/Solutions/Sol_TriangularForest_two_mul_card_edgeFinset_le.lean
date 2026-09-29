-- Prove2me | solution 1 for TriangularForest.two_mul_card_edgeFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:18:33.781931+00:00
-- url     : https://prove2.me/submissions/97149468-325b-4ffe-ab82-4969c7e728c7

import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs
open TriangularForest SimpleGraph Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsTriangularForest G) (hcard : 1 ≤ Fintype.card V) :
    2 * #G.edgeFinset ≤ 3 * (Fintype.card V - 1) := by
  classical
  -- induced subgraphs of triangular forests are triangular forests
  have hind : ∀ {W : Type u_1} {H : SimpleGraph W} (s : Set W),
      IsTriangularForest H → IsTriangularForest (H.induce s) := by
    intro W H s hH v c hc
    have hinj : Function.Injective (Embedding.induce (G := H) s).toHom :=
      (Embedding.induce (G := H) s).injective
    have hmap := hH (c.map (Embedding.induce (G := H) s).toHom)
      ((Walk.map_isCycle_iff_of_injective hinj).mpr hc)
    rwa [Walk.length_map] at hmap
  -- the leaf triangle lemma: minimum degree `≥ 2` forces an edge with both degrees `≤ 2`
  have leaf : ∀ (W : Type u_1) [Fintype W] [DecidableEq W] [Nonempty W] (H : SimpleGraph W)
      [DecidableRel H.Adj], IsTriangularForest H → (∀ v, 2 ≤ H.degree v) →
      ∃ u v : W, H.Adj u v ∧ H.degree u ≤ 2 ∧ H.degree v ≤ 2 := by
    intro W _ _ _ H _ hG hmin
    classical
    -- a longest path `p : a ⟶ b`
    obtain ⟨v0⟩ := ‹Nonempty W›
    let P : ℕ → Prop := fun n => ∃ (x y : W) (q : H.Walk x y), q.IsPath ∧ q.length = n
    have hP0 : P 0 := ⟨v0, v0, Walk.nil, Walk.IsPath.nil, rfl⟩
    have hbound : ∀ n, P n → n ≤ Fintype.card W := by
      rintro n ⟨x, y, q, hq, rfl⟩
      exact hq.length_lt.le
    obtain ⟨a, b, p, hp, hpN⟩ : P (Nat.findGreatest P (Fintype.card W)) :=
      Nat.findGreatest_spec (Nat.zero_le _) hP0
    have hmax : ∀ (x y : W) (q : H.Walk x y), q.IsPath → q.length ≤ p.length := by
      intro x y q hq
      rw [hpN]
      exact Nat.le_findGreatest (hbound _ ⟨x, y, q, hq, rfl⟩) ⟨x, y, q, hq, rfl⟩
    -- neighbours of the start `a` lie on the path, else prepending one lengthens it
    have hon : ∀ x, H.Adj a x → x ∈ p.support := by
      intro x hax
      by_contra hnot
      have hpath : (Walk.cons (H.symm hax) p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
      have := hmax x b _ hpath
      rw [Walk.length_cons] at this
      omega
    have hdeg_a := hmin a
    obtain ⟨x0, hx0⟩ : ∃ x, H.Adj a x := by
      have : 0 < (H.neighborFinset a).card := by rw [card_neighborFinset_eq_degree]; omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp this
      exact ⟨x, (H.mem_neighborFinset a x).mp hx⟩
    cases p with
    | nil =>
      have := hon x0 hx0
      simp at this
      exact absurd this.symm (H.ne_of_adj hx0)
    | @cons _ v₁ _ h1 p1 =>
      cases p1 with
      | nil =>
        -- the path is a single edge, so `a` has at most one neighbour
        have hsub : H.neighborFinset a ⊆ {x0} := by
          intro x hx
          have hax := (H.mem_neighborFinset a x).mp hx
          have h1x := hon x hax
          have h10 := hon x0 hx0
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at h1x h10
          rcases h1x with h | h
          · exact absurd h.symm (H.ne_of_adj hax)
          rcases h10 with h' | h'
          · exact absurd h'.symm (H.ne_of_adj hx0)
          rw [Finset.mem_singleton, h, h']
        have := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree, Finset.card_singleton] at this
        omega
      | @cons _ v₂ _ h2 r =>
        have hp' := hp
        rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff] at hp'
        obtain ⟨⟨hr, hv₁r⟩, ha⟩ := hp'
        rw [Walk.support_cons, List.mem_cons, not_or] at ha
        obtain ⟨hav₁, har⟩ := ha
        have hv₂r : v₂ ∈ r.support := Walk.start_mem_support r
        -- every neighbour of `a` is `v₁` or `v₂`: a later one closes a cycle of length ≥ 4
        have hnbr_a : ∀ x, H.Adj a x → x = v₁ ∨ x = v₂ := by
          intro x hax
          have hx := hon x hax
          rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hx
          rcases hx with hxa | hxv₁ | hxr
          · exact absurd hxa.symm (H.ne_of_adj hax)
          · exact Or.inl hxv₁
          · by_cases hxv₂ : x = v₂
            · exact Or.inr hxv₂
            exfalso
            have hq : (r.takeUntil x hxr).IsPath := hr.takeUntil hxr
            have hqsub : ∀ z ∈ (r.takeUntil x hxr).support, z ∈ r.support :=
              fun z hz => Walk.support_takeUntil_subset_support r hxr hz
            have hqlen : (r.takeUntil x hxr).length ≠ 0 := by
              intro h0
              exact hxv₂ (Walk.eq_of_length_eq_zero h0).symm
            have hW : (Walk.cons h1 (Walk.cons h2 (r.takeUntil x hxr))).IsPath := by
              rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
              refine ⟨⟨hq, fun h => hv₁r (hqsub _ h)⟩, ?_⟩
              rw [Walk.support_cons, List.mem_cons, not_or]
              exact ⟨hav₁, fun h => har (hqsub _ h)⟩
            have hE : s(x, a) ∉ (Walk.cons h1 (Walk.cons h2 (r.takeUntil x hxr))).edges := by
              rw [Walk.edges_cons, Walk.edges_cons, List.mem_cons, List.mem_cons]
              rintro (h | h | h)
              · rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨h', _⟩
                · exact H.ne_of_adj hax h'.symm
                · exact hv₁r (h' ▸ hxr)
              · rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨_, h'⟩
                · exact har (h' ▸ hv₂r)
                · exact hav₁ h'
              · exact har (hqsub _ (Walk.snd_mem_support_of_mem_edges _ h))
            have hcyc := (Walk.cons_isCycle_iff _ (H.symm hax)).mpr ⟨hW, hE⟩
            have h3 := hG _ hcyc
            simp only [Walk.length_cons] at h3
            omega
        have hsubA : H.neighborFinset a ⊆ {v₁, v₂} := by
          intro x hx
          rcases hnbr_a x ((H.mem_neighborFinset a x).mp hx) with h | h <;> simp [h]
        have hdegA : H.degree a ≤ 2 := by
          rw [← card_neighborFinset_eq_degree]
          exact (Finset.card_le_card hsubA).trans Finset.card_le_two
        have heqA : H.neighborFinset a = {v₁, v₂} :=
          Finset.eq_of_subset_of_card_le hsubA
            (by rw [card_neighborFinset_eq_degree]; exact Finset.card_le_two.trans hdeg_a)
        have hav₂ : H.Adj a v₂ := (H.mem_neighborFinset a v₂).mp (by rw [heqA]; simp)
        -- every neighbour of `v₁` is `a` or `v₂`
        have hnbr_v₁ : ∀ y, H.Adj v₁ y → y = a ∨ y = v₂ := by
          intro y hy
          by_cases hya : y = a
          · exact Or.inl hya
          by_cases hyv₂ : y = v₂
          · exact Or.inr hyv₂
          exfalso
          have hyv₁ : y ≠ v₁ := fun h => H.ne_of_adj hy h.symm
          by_cases hyr : y ∈ r.support
          · -- the cycle `v₁ → v₂ ⋯ y → v₁` is a triangle, so `v₂ ~ y`
            have hq : (r.takeUntil y hyr).IsPath := hr.takeUntil hyr
            have hqsub : ∀ z ∈ (r.takeUntil y hyr).support, z ∈ r.support :=
              fun z hz => Walk.support_takeUntil_subset_support r hyr hz
            have hW : (Walk.cons h2 (r.takeUntil y hyr)).IsPath :=
              (Walk.cons_isPath_iff _ _).mpr ⟨hq, fun h => hv₁r (hqsub _ h)⟩
            have hE : s(y, v₁) ∉ (Walk.cons h2 (r.takeUntil y hyr)).edges := by
              rw [Walk.edges_cons, List.mem_cons]
              rintro (h | h)
              · rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨h', _⟩
                · exact hyv₁ h'
                · exact hyv₂ h'
              · exact hv₁r (hqsub _ (Walk.snd_mem_support_of_mem_edges _ h))
            have hcyc := (Walk.cons_isCycle_iff _ (H.symm hy)).mpr ⟨hW, hE⟩
            have h3 := hG _ hcyc
            simp only [Walk.length_cons] at h3
            have hq1 : (r.takeUntil y hyr).length = 1 := by omega
            have hv₂y : H.Adj v₂ y := Walk.adj_of_length_eq_one hq1
            -- then `a → v₁ → y → v₂ → a` is a 4-cycle
            have d1 : a ≠ v₁ := hav₁
            have d2 : a ≠ v₂ := H.ne_of_adj hav₂
            have d3 : a ≠ y := fun h => hya h.symm
            have d4 : v₁ ≠ y := fun h => hyv₁ h.symm
            have d5 : v₁ ≠ v₂ := H.ne_of_adj h2
            have d6 : y ≠ v₂ := hyv₂
            have hC : (Walk.cons h1 (Walk.cons hy (Walk.cons (H.symm hv₂y)
                (Walk.cons (H.symm hav₂) Walk.nil)))).IsCycle := by
              rw [Walk.cons_isCycle_iff]
              constructor
              · simp [Walk.cons_isPath_iff, d1, d2, d3, d4, d5, d6, d1.symm, d2.symm, d3.symm,
                  d4.symm, d5.symm, d6.symm]
              · simp [Sym2.eq_iff, d1, d2, d3, d4, d5, d6, d1.symm, d2.symm, d3.symm,
                  d4.symm, d5.symm, d6.symm]
            have h4 := hG _ hC
            simp at h4
          · -- `y` is off the path: `y → v₁ → a → v₂ ⋯ b` is a longer path
            have hpath : (Walk.cons (H.symm hy) (Walk.cons (H.symm h1) (Walk.cons hav₂ r))).IsPath := by
              rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff]
              refine ⟨⟨⟨hr, har⟩, ?_⟩, ?_⟩
              · rw [Walk.support_cons, List.mem_cons, not_or]
                exact ⟨fun h => hav₁ h.symm, hv₁r⟩
              · rw [Walk.support_cons, List.mem_cons, not_or, Walk.support_cons, List.mem_cons,
                  not_or]
                exact ⟨hyv₁, hya, hyr⟩
            have := hmax y b _ hpath
            simp only [Walk.length_cons] at this
            omega
        have hsubV : H.neighborFinset v₁ ⊆ {a, v₂} := by
          intro y hy
          rcases hnbr_v₁ y ((H.mem_neighborFinset v₁ y).mp hy) with h | h <;> simp [h]
        have hdegV : H.degree v₁ ≤ 2 := by
          rw [← card_neighborFinset_eq_degree]
          exact (Finset.card_le_card hsubV).trans Finset.card_le_two
        exact ⟨a, v₁, h1, hdegA, hdegV⟩

  -- deleting a vertex removes exactly its degree in edges
  have hdel : ∀ (W : Type u_1) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj] (x : W),
      #(H.induce ({x}ᶜ : Set W)).edgeFinset + H.degree x = #H.edgeFinset := by
    intro W _ _ H _ x
    have h1 := card_edgeFinset_induce_compl_singleton H x
    have h2 := card_edgeFinset_deleteIncidenceSet H x
    have h3 : H.degree x ≤ #H.edgeFinset := by
      rw [← card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (H.incidenceFinset_subset x)
    omega
  have hcardc : ∀ (W : Type u_1) [Fintype W] [DecidableEq W] (x : W),
      Fintype.card ↥({x}ᶜ : Set W) = Fintype.card W - 1 := by
    intro W _ _ x
    rw [Fintype.card_compl_set]
    simp
  -- strong induction on the number of vertices
  suffices main : ∀ n, ∀ (W : Type u_1) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], IsTriangularForest H → Fintype.card W = n → 1 ≤ n →
      2 * #H.edgeFinset ≤ 3 * (n - 1) from main _ V G hG rfl hcard
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  -- deleting a vertex of degree `≤ 1` from a graph on `m ≤ n` vertices
  have caseA : ∀ (W : Type u_1) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], IsTriangularForest H → Fintype.card W ≤ n → 2 ≤ Fintype.card W →
      ∀ x : W, H.degree x ≤ 1 → 2 * #H.edgeFinset + 1 ≤ 3 * (Fintype.card W - 1) := by
    intro W _ _ H _ hH hle h2 x hx
    have hc := hcardc W x
    have hIH := ih (Fintype.card W - 1) (by omega) (↥({x}ᶜ : Set W)) (H.induce ({x}ᶜ : Set W))
      (hind _ hH) hc (by omega)
    have hd := hdel W H x
    omega
  intro W _ _ H _ hH hWn hn1
  by_cases hlow : ∃ x : W, H.degree x ≤ 1
  · obtain ⟨x, hx⟩ := hlow
    by_cases hn2 : 2 ≤ n
    · have := caseA W H hH hWn.le (hWn ▸ hn2) x hx
      rw [hWn] at this
      omega
    · -- a single vertex carries no edge
      have hn : n = 1 := by omega
      have h0 : Nat.choose 1 2 = 0 := by decide
      have := H.card_edgeFinset_le_card_choose_two
      rw [hWn, hn, h0] at this
      rw [hn]
      omega
  · push Not at hlow
    have hmin : ∀ v, 2 ≤ H.degree v := fun v => hlow v
    haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨u, v, huv, hu, hv⟩ := leaf W H hH hmin
    have hu2 : H.degree u = 2 := le_antisymm hu (hmin u)
    have hn3 : 3 ≤ n := by
      have := H.degree_lt_card_verts u
      omega
    -- delete `u`; in what remains `v` has degree `≤ 1`
    have hvu : v ∈ ({u}ᶜ : Set W) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (H.ne_of_adj huv).symm
    have hdeg1 : (H.induce ({u}ᶜ : Set W)).degree ⟨v, hvu⟩ ≤ 1 := by
      rw [← card_neighborFinset_eq_degree]
      have hsub : ((H.induce ({u}ᶜ : Set W)).neighborFinset ⟨v, hvu⟩).map
          (Function.Embedding.subtype _) ⊆ (H.neighborFinset v).erase u := by
        intro w hw
        rw [Finset.mem_map] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        rw [mem_neighborFinset] at hw'
        simp only [Function.Embedding.coe_subtype]
        rw [Finset.mem_erase, mem_neighborFinset]
        exact ⟨w'.2, hw'⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_map, Finset.card_erase_of_mem ((H.mem_neighborFinset v u).mpr (H.symm huv)),
        card_neighborFinset_eq_degree H v] at this
      omega
    have hc := hcardc W u
    have hA := caseA _ (H.induce ({u}ᶜ : Set W)) (hind _ hH) (by omega) (by omega) ⟨v, hvu⟩ hdeg1
    have hd := hdel W H u
    omega
