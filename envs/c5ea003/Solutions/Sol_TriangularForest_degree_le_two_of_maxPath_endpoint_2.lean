-- Prove2me | solution 2 for TriangularForest.degree_le_two_of_maxPath_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:44:11.451331+00:00
-- url     : https://prove2.me/submissions/67df884c-c292-430e-a356-90b0288c32c7

import Definitions.Def_Logic_TriangularForest_Defs

open SimpleGraph TriangularForest

open SimpleGraph TriangularForest in
/-- **An endpoint of a longest path in a triangular forest has degree at most 2.** -/
theorem solution {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : IsTriangularForest G) {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length) :
    G.degree a ≤ 2 := by
  classical
  have hon : ∀ w, G.Adj a w → w ∈ p.support := by
    intro w haw
    by_contra hw
    have hpath : (Walk.cons haw.symm p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hw⟩
    have hl := hmax w b _ hpath
    rw [Walk.length_cons] at hl
    omega
  have hpos : ∀ w (haw : G.Adj a w), 1 ≤ (p.takeUntil w (hon w haw)).length := by
    intro w haw
    by_contra h0
    have hl : (p.takeUntil w (hon w haw)).length = 0 := by omega
    have e := Walk.getVert_length_takeUntil (p := p) (hon w haw)
    rw [hl, Walk.getVert_zero] at e
    exact haw.ne e
  have hle2 : ∀ w (haw : G.Adj a w), (p.takeUntil w (hon w haw)).length ≤ 2 := by
    intro w haw
    by_contra h3
    have hqpath : (p.takeUntil w (hon w haw)).IsPath := hp.takeUntil (hon w haw)
    have hnot : s(a, w) ∉ (p.takeUntil w (hon w haw)).reverse.edges := by
      rw [Walk.edges_reverse, List.mem_reverse]
      intro hmem
      have hsnd := hqpath.eq_snd_of_mem_edges hmem
      have h1 : (p.takeUntil w (hon w haw)).getVert 1 = w := hsnd.symm
      have h2 := Walk.getVert_length (p.takeUntil w (hon w haw))
      have hinj := hqpath.getVert_injOn (show 1 ≤ (p.takeUntil w (hon w haw)).length by omega)
        (show (p.takeUntil w (hon w haw)).length ≤ (p.takeUntil w (hon w haw)).length from le_rfl)
        (h1.trans h2.symm)
      omega
    have hcyc : (Walk.cons haw (p.takeUntil w (hon w haw)).reverse).IsCycle :=
      (Walk.cons_isCycle_iff _ _).mpr ⟨(Walk.isPath_reverse_iff _).mpr hqpath, hnot⟩
    have hl := hG _ hcyc
    rw [Walk.length_cons, Walk.length_reverse] at hl
    omega
  rw [← G.card_neighborFinset_eq_degree a]
  let f : V → ℕ := fun w => if h : G.Adj a w then (p.takeUntil w (hon w h)).length else 0
  calc (G.neighborFinset a).card ≤ ({1, 2} : Finset ℕ).card := by
        apply Finset.card_le_card_of_injOn f
        · intro w hw
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw
          have h1 := hpos w hw
          have h2 := hle2 w hw
          simp only [f, dif_pos hw, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          omega
        · intro w1 hw1 w2 hw2 heq
          rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw1 hw2
          simp only [f, dif_pos hw1, dif_pos hw2] at heq
          have e1 := Walk.getVert_length_takeUntil (p := p) (hon w1 hw1)
          have e2 := Walk.getVert_length_takeUntil (p := p) (hon w2 hw2)
          rw [← e1, ← e2, heq]
    _ = 2 := rfl
