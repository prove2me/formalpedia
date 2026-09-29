-- Prove2me | solution 2 for TriangularForest.maxPath_neighbor_idx
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:26:26.876393+00:00
-- url     : https://prove2.me/submissions/5ab2f58f-68c9-4177-be71-f9b9b3970b1b

import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs
open TriangularForest SimpleGraph Finset in
theorem solution {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {a b : V} (hG : IsTriangularForest G) (p : G.Walk a b)
    (hp : p.IsPath) (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {x : V} (hx : x ∈ G.neighborFinset a) :
    p.support.idxOf x = 1 ∨ p.support.idxOf x = 2 := by
  have hadj : G.Adj a x := (G.mem_neighborFinset a x).mp hx
  -- a path using the edge `xa` somewhere must be that single edge
  have key : ∀ {u w : V} (r : G.Walk u w), r.IsPath → s(w, u) ∈ r.edges → r.length = 1 := by
    intro u w r hr h
    induction r with
    | nil => simp at h
    | @cons u' c w' hadj' r' _ =>
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h
      rw [SimpleGraph.Walk.cons_isPath_iff] at hr
      rcases h with he | he
      · have hc : c = w' := by
          rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h2 (G.ne_of_adj hadj')
          · exact h1.symm
        subst hc
        have hnil : r' = SimpleGraph.Walk.nil := (SimpleGraph.Walk.isPath_iff_eq_nil r').mp hr.1
        rw [SimpleGraph.Walk.length_cons, hnil]
        simp
      · exact absurd (SimpleGraph.Walk.snd_mem_support_of_mem_edges r' he) hr.2
  -- `x` lies on the maximal path, else prepending `x` would lengthen it
  have hmem : x ∈ p.support := by
    by_contra hnot
    have hpath : (SimpleGraph.Walk.cons (G.symm hadj) p).IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
    have := hmax x b _ hpath
    rw [SimpleGraph.Walk.length_cons] at this
    omega
  -- the initial segment of `p` up to `x` is a path of length `idxOf x`
  set q := p.takeUntil x hmem with hqdef
  have hq : q.IsPath := hp.takeUntil hmem
  have hlen : q.length = p.support.idxOf x := SimpleGraph.Walk.length_takeUntil p hmem
  rw [← hlen]
  by_cases he : s(x, a) ∈ q.edges
  · exact Or.inl (key q hq he)
  · -- closing `q` with the edge `xa` gives a cycle, which must be a triangle
    have hcyc : (SimpleGraph.Walk.cons (G.symm hadj) q).IsCycle :=
      (SimpleGraph.Walk.cons_isCycle_iff q (G.symm hadj)).mpr ⟨hq, he⟩
    have h3 := hG _ hcyc
    rw [SimpleGraph.Walk.length_cons] at h3
    right
    omega
