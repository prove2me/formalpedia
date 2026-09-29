-- Prove2me | solution 1 for TriangularForest.degree_second_le_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:48:57.537861+00:00
-- url     : https://prove2.me/submissions/84715c91-e5bf-45ef-9521-f459bf871c67

-- Sol generated from Logic/TriangularForest/SharpBound.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs

/-!
# The sharp sparsity bound for triangular forests

A connected triangular forest on `n` vertices with `t` triangular blocks has `n - 1 + t` edges
and `2t ≤ n - 1`, so `2e ≤ 3(n-1)`.  Here we prove this sharp bound
(`TriangularForest.two_mul_card_edgeFinset_le`) without developing block decompositions, by
refining the longest-path argument of `Logic.TriangularForest.Sparsity`:

* `TriangularForest.degree_second_le_two` — if `p = a → v₁ → v₂ → ⋯` is a longest path in a
  triangular forest and `a` is also adjacent to `v₂` (which happens as soon as `a` has degree
  two), then the *second* vertex `v₁` also has degree at most two.  Neighbours of `v₁` off the
  path would allow the reroute `y → v₁ → a → v₂ → ⋯`, which is longer; neighbours further along
  the path close a cycle of length `≥ 4`, except for the vertex `v₃`, which is excluded by the
  4-cycle `a → v₁ → v₃ → v₂ → a`.
* `TriangularForest.exists_adj_degree_le_two` — hence a triangular forest of minimum degree at
  least two contains an *edge* both of whose endpoints have degree two (a leaf triangle).
* Deleting such a pair removes two vertices and exactly three edges, which powers the induction
  giving `2e ≤ 3(n-1)`.

As a consequence `Kₙ` fails to decompose into two triangular forests already for `n ≥ 6`, which
combined with `TriangularForest.completeGraph_decomposesIntoTwo_five` pins the threshold
exactly: `Kₙ` decomposes into two triangular forests if and only if `n ≤ 5`.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}



variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]















open TriangularForest in
theorem solution(hG : IsTriangularForest G)
    {a v₁ v₂ b : V} (h₀₁ : G.Adj a v₁) (h₁₂ : G.Adj v₁ v₂) (r : G.Walk v₂ b)
    (hp : (Walk.cons h₀₁ (Walk.cons h₁₂ r)).IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath →
      q.length ≤ (Walk.cons h₀₁ (Walk.cons h₁₂ r)).length)
    (ha₂ : G.Adj a v₂) : G.degree v₁ ≤ 2 := by
  classical
  have hp₁ : (Walk.cons h₁₂ r).IsPath := ((Walk.cons_isPath_iff _ _).1 hp).1
  have hr : r.IsPath := ((Walk.cons_isPath_iff _ _).1 hp₁).1
  have hv₁r : v₁ ∉ r.support := ((Walk.cons_isPath_iff _ _).1 hp₁).2
  have har : a ∉ (Walk.cons h₁₂ r).support := ((Walk.cons_isPath_iff _ _).1 hp).2
  have har' : a ∉ r.support := fun h => har (by simp [Walk.support_cons, h])
  have hsub : G.neighborFinset v₁ ⊆ {a, v₂} := by
    intro y hy
    have hadj : G.Adj v₁ y := (G.mem_neighborFinset v₁ y).1 hy
    by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    obtain ⟨hya, hyv₂⟩ := hcon
    have hyv₁ : y ≠ v₁ := hadj.ne'
    have e1 : a ≠ v₁ := h₀₁.ne
    have e2 : a ≠ v₂ := ha₂.ne
    have e3 : a ≠ y := fun h => hya h.symm
    have e4 : v₁ ≠ v₂ := h₁₂.ne
    have e5 : v₁ ≠ y := hadj.ne
    have e6 : v₂ ≠ y := fun h => hyv₂ h.symm
    -- Step 1: `y` lies on the tail `r` of the path.
    have hys : y ∈ r.support := by
      by_contra hnot
      have hnew : (Walk.cons hadj.symm (Walk.cons h₀₁.symm (Walk.cons ha₂ r))).IsPath := by
        rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.cons_isPath_iff]
        refine ⟨⟨⟨hr, har'⟩, ?_⟩, ?_⟩
        · simp only [Walk.support_cons, List.mem_cons, not_or]
          exact ⟨e1.symm, hv₁r⟩
        · simp only [Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hyv₁, e3.symm, hnot⟩
      have hlen := hmax _ _ _ hnew
      simp [Walk.length_cons] at hlen
    -- Step 2: `y` sits at position `m + 2` of the path, with `m ≥ 1`.
    set q := r.takeUntil y hys with hq
    have hqp : q.IsPath := hr.takeUntil hys
    have hqv₁ : v₁ ∉ q.support := fun h => hv₁r (r.support_takeUntil_subset hys h)
    have hqlen : q.length ≠ 0 := by
      intro h0
      exact hyv₂ (((r.nil_takeUntil hys).1 (Walk.nil_iff_length_eq.2 h0)).symm)
    rcases Nat.lt_or_ge q.length 2 with hm1 | hm2
    · -- `y` is the vertex `v₃` right after `v₂`: the 4-cycle `a → v₁ → y → v₂ → a` is forbidden.
      have hlen1 : q.length = 1 := by omega
      have hrlen : 0 < r.length := by
        have hle := r.length_takeUntil_le hys
        rw [← hq] at hle
        omega
      have hy1 : r.getVert 1 = y := by
        have := r.getVert_support_idxOf hys
        rwa [← r.length_takeUntil hys, ← hq, hlen1] at this
      have hv₂y : G.Adj v₂ y := by
        have := r.adj_getVert_succ (i := 0) hrlen
        simpa [hy1] using this
      have hcyc : (Walk.cons h₀₁ (Walk.cons hadj (Walk.cons hv₂y.symm
          (Walk.cons ha₂.symm Walk.nil)))).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        refine ⟨?_, ?_⟩
        · simp [Walk.isPath_def, e4, e5, e1.symm, e2.symm, e3.symm, e6.symm]
        · simp [e1, e2, e3, e4, e5, e1.symm]
      have hcl := hG _ hcyc
      simp only [Walk.length_cons, Walk.length_nil] at hcl
      omega
    · -- `y` is further along: it closes a cycle of length `q.length + 2 ≥ 4`.
      have hedge : s(y, v₁) ∉ (Walk.cons h₁₂ q).edges := by
        simp only [Walk.edges_cons, List.mem_cons, Sym2.eq_iff, not_or]
        refine ⟨by simp [e4, e5.symm, e6.symm], ?_⟩
        intro hmem
        exact hqv₁ (Walk.snd_mem_support_of_mem_edges q hmem)
      have hcyc : (Walk.cons hadj.symm (Walk.cons h₁₂ q)).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        refine ⟨?_, hedge⟩
        rw [Walk.cons_isPath_iff]
        exact ⟨hqp, hqv₁⟩
      have hcl := hG _ hcyc
      simp only [Walk.length_cons] at hcl
      omega
  calc G.degree v₁ = #(G.neighborFinset v₁) := (card_neighborFinset_eq_degree G v₁).symm
    _ ≤ #({a, v₂} : Finset V) := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
