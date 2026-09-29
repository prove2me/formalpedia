-- Prove2me | solution 1 for TriangularForest.length_eq_one_of_mem_edges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:30:34.162974+00:00
-- url     : https://prove2.me/submissions/b6657f17-8549-4f1f-b6c9-86941268ad65

import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs
open TriangularForest SimpleGraph Finset in
theorem solution {V : Type*} {G : SimpleGraph V} {a x : V} (q : G.Walk a x) (hq : q.IsPath)
    (h : s(x, a) ∈ q.edges) : q.length = 1 := by
  induction q with
  | nil => simp at h
  | @cons u b w hadj p ih =>
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h
    rw [SimpleGraph.Walk.cons_isPath_iff] at hq
    rcases h with he | he
    · -- the traversed edge IS the first step, so `w = b` and the rest is a loop path
      have hb : b = w := by
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h2 (G.ne_of_adj hadj)
        · exact h1.symm
      subst hb
      have hnil : p = SimpleGraph.Walk.nil := (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hq.1
      rw [SimpleGraph.Walk.length_cons, hnil]
      simp
    · -- otherwise `u` would be revisited, contradicting `IsPath`
      exact absurd (SimpleGraph.Walk.snd_mem_support_of_mem_edges p he) hq.2
