-- Prove2me | solution 2 for TriangularForest.exists_adj_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:21:57.404642+00:00
-- url     : https://prove2.me/submissions/d9fb1718-25b5-42c3-a1bd-9e39e8d6bdac

import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs
open TriangularForest SimpleGraph Finset in
theorem solution {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] (hG : IsTriangularForest G)
    (hmin : ∀ v : V, 2 ≤ G.degree v) :
    ∃ u v : V, G.Adj u v ∧ G.degree u ≤ 2 ∧ G.degree v ≤ 2 := by
  classical
  -- a longest path `p : a ⟶ b`
  obtain ⟨v0⟩ := ‹Nonempty V›
  let P : ℕ → Prop := fun n => ∃ (x y : V) (q : G.Walk x y), q.IsPath ∧ q.length = n
  have hP0 : P 0 := ⟨v0, v0, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hbound : ∀ n, P n → n ≤ Fintype.card V := by
    rintro n ⟨x, y, q, hq, rfl⟩
    exact hq.length_lt.le
  obtain ⟨a, b, p, hp, hpN⟩ : P (Nat.findGreatest P (Fintype.card V)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length := by
    intro x y q hq
    rw [hpN]
    exact Nat.le_findGreatest (hbound _ ⟨x, y, q, hq, rfl⟩) ⟨x, y, q, hq, rfl⟩
  -- neighbours of the start `a` lie on the path, else prepending one lengthens it
  have hon : ∀ x, G.Adj a x → x ∈ p.support := by
    intro x hax
    by_contra hnot
    have hpath : (Walk.cons (G.symm hax) p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
    have := hmax x b _ hpath
    rw [Walk.length_cons] at this
    omega
  have hdeg_a := hmin a
  obtain ⟨x0, hx0⟩ : ∃ x, G.Adj a x := by
    have : 0 < (G.neighborFinset a).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp this
    exact ⟨x, (G.mem_neighborFinset a x).mp hx⟩
  cases p with
  | nil =>
    have := hon x0 hx0
    simp at this
    exact absurd this.symm (G.ne_of_adj hx0)
  | @cons _ v₁ _ h1 p1 =>
    cases p1 with
    | nil =>
      -- the path is a single edge, so `a` has at most one neighbour
      have hsub : G.neighborFinset a ⊆ {x0} := by
        intro x hx
        have hax := (G.mem_neighborFinset a x).mp hx
        have h1x := hon x hax
        have h10 := hon x0 hx0
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at h1x h10
        rcases h1x with h | h
        · exact absurd h.symm (G.ne_of_adj hax)
        rcases h10 with h' | h'
        · exact absurd h'.symm (G.ne_of_adj hx0)
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
      have hnbr_a : ∀ x, G.Adj a x → x = v₁ ∨ x = v₂ := by
        intro x hax
        have hx := hon x hax
        rw [Walk.support_cons, Walk.support_cons, List.mem_cons, List.mem_cons] at hx
        rcases hx with hxa | hxv₁ | hxr
        · exact absurd hxa.symm (G.ne_of_adj hax)
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
              · exact G.ne_of_adj hax h'.symm
              · exact hv₁r (h' ▸ hxr)
            · rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨_, h'⟩
              · exact har (h' ▸ hv₂r)
              · exact hav₁ h'
            · exact har (hqsub _ (Walk.snd_mem_support_of_mem_edges _ h))
          have hcyc := (Walk.cons_isCycle_iff _ (G.symm hax)).mpr ⟨hW, hE⟩
          have h3 := hG _ hcyc
          simp only [Walk.length_cons] at h3
          omega
      have hsubA : G.neighborFinset a ⊆ {v₁, v₂} := by
        intro x hx
        rcases hnbr_a x ((G.mem_neighborFinset a x).mp hx) with h | h <;> simp [h]
      have hdegA : G.degree a ≤ 2 := by
        rw [← card_neighborFinset_eq_degree]
        exact (Finset.card_le_card hsubA).trans Finset.card_le_two
      have heqA : G.neighborFinset a = {v₁, v₂} :=
        Finset.eq_of_subset_of_card_le hsubA
          (by rw [card_neighborFinset_eq_degree]; exact Finset.card_le_two.trans hdeg_a)
      have hav₂ : G.Adj a v₂ := (G.mem_neighborFinset a v₂).mp (by rw [heqA]; simp)
      -- every neighbour of `v₁` is `a` or `v₂`
      have hnbr_v₁ : ∀ y, G.Adj v₁ y → y = a ∨ y = v₂ := by
        intro y hy
        by_cases hya : y = a
        · exact Or.inl hya
        by_cases hyv₂ : y = v₂
        · exact Or.inr hyv₂
        exfalso
        have hyv₁ : y ≠ v₁ := fun h => G.ne_of_adj hy h.symm
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
          have hcyc := (Walk.cons_isCycle_iff _ (G.symm hy)).mpr ⟨hW, hE⟩
          have h3 := hG _ hcyc
          simp only [Walk.length_cons] at h3
          have hq1 : (r.takeUntil y hyr).length = 1 := by omega
          have hv₂y : G.Adj v₂ y := Walk.adj_of_length_eq_one hq1
          -- then `a → v₁ → y → v₂ → a` is a 4-cycle
          have d1 : a ≠ v₁ := hav₁
          have d2 : a ≠ v₂ := G.ne_of_adj hav₂
          have d3 : a ≠ y := fun h => hya h.symm
          have d4 : v₁ ≠ y := fun h => hyv₁ h.symm
          have d5 : v₁ ≠ v₂ := G.ne_of_adj h2
          have d6 : y ≠ v₂ := hyv₂
          have hC : (Walk.cons h1 (Walk.cons hy (Walk.cons (G.symm hv₂y)
              (Walk.cons (G.symm hav₂) Walk.nil)))).IsCycle := by
            rw [Walk.cons_isCycle_iff]
            constructor
            · simp [Walk.cons_isPath_iff, d1, d2, d3, d4, d5, d6, d1.symm, d2.symm, d3.symm,
                d4.symm, d5.symm, d6.symm]
            · simp [Sym2.eq_iff, d1, d2, d3, d4, d5, d6, d1.symm, d2.symm, d3.symm,
                d4.symm, d5.symm, d6.symm]
          have h4 := hG _ hC
          simp at h4
        · -- `y` is off the path: `y → v₁ → a → v₂ ⋯ b` is a longer path
          have hpath : (Walk.cons (G.symm hy) (Walk.cons (G.symm h1) (Walk.cons hav₂ r))).IsPath := by
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
      have hsubV : G.neighborFinset v₁ ⊆ {a, v₂} := by
        intro y hy
        rcases hnbr_v₁ y ((G.mem_neighborFinset v₁ y).mp hy) with h | h <;> simp [h]
      have hdegV : G.degree v₁ ≤ 2 := by
        rw [← card_neighborFinset_eq_degree]
        exact (Finset.card_le_card hsubV).trans Finset.card_le_two
      exact ⟨a, v₁, h1, hdegA, hdegV⟩
