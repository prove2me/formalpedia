-- Prove2me | solution 1 for ChordalRegAlloc.colorable_of_earlierDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:04:25.916386+00:00
-- url     : https://prove2.me/submissions/f02dd026-d7c4-4f09-8e77-eafa43184884

-- Sol generated from Bridges/ChordalRegisterAllocation.lean
import Mathlib
import Definitions.Def_Bridges_ChordalRegisterAllocation
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Register allocation for SSA programs: chordal interference graphs are perfect

Register allocation assigns program variables to a fixed bank of CPU registers.  Two
variables *interfere* when they are simultaneously live; a legal assignment gives interfering
variables distinct registers, i.e. a proper colouring of the **interference graph** `G`, using
`χ(G)` colours in the optimum.

For programs in **Static Single Assignment (SSA)** form the interference graph is *chordal*:
every cycle of length `≥ 4` has a chord.  Equivalently, `G` admits a **perfect elimination
ordering (PEO)** — an enumeration `v₁, …, vₙ` of the vertices such that, for each `vᵢ`, the
neighbours of `vᵢ` occurring *earlier* in the order form a clique.  This file proves the
central structural fact behind optimal SSA register allocation:

> **Chordal graphs are perfect.**  If `G` has a perfect elimination ordering then
> `χ(G) = ω(G)`: greedy colouring along the order uses exactly `ω(G) = ` (the maximum number
> of simultaneously live variables) registers, and no colouring can do better.

We work with the concrete elimination order given by the linear order on `Fin n`, so a PEO is
the hypothesis `IsPerfectElimOrder G : ∀ v, G.IsClique (earlierNeighbours G v)`.

## Main results

* `colorable_of_earlierDegree_lt` — the **greedy colouring lemma**: if every vertex has fewer
  than `k` earlier neighbours, then `G` is `k`-colourable (no chordality needed).
* `earlier_insert_isClique`, `earlierDegree_succ_le_cliqueNum` — under a PEO each vertex with
  its earlier neighbours is a clique, so `earlierDegree v + 1 ≤ ω(G)`.
* `colorable_cliqueNum_of_peo` — a PEO graph is `ω(G)`-colourable (linear-scan optimality).
* `chromaticNumber_eq_cliqueNum_of_peo` — **perfectness of chordal graphs**: `χ(G) = ω(G)`.

## Interval graphs as a special case

Interval / linear-scan interference graphs (variables with contiguous live ranges) are a
strict subclass of chordal graphs.  We recover them:

* `interferenceGraph_isPEO` — when live ranges are sorted by start point (`Monotone lo`), the
  interval interference graph has a perfect elimination ordering;
* `interval_chromaticNumber_eq_cliqueNum` — hence `χ = ω` for interval graphs, obtained here
  purely as a corollary of the general chordal theorem.

This strictly generalises the interval-graph analysis of register allocation to the full SSA
(chordal) setting: interval ⊊ chordal, and the optimal register count is the clique number in
both.
-/

open Finset SimpleGraph

open ChordalRegAlloc

variable {n : ℕ}


@[simp] lemma mem_earlierNeighbours {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v w : Fin n} : w ∈ earlierNeighbours G v ↔ w < v ∧ G.Adj v w := by
  simp [earlierNeighbours]


/-
**Greedy colouring lemma.**  If every vertex has strictly fewer than `k` earlier
neighbours, then `G` is `k`-colourable.  Processing vertices from largest to smallest, when a
vertex is coloured its already-coloured neighbours are exactly its earlier neighbours, of
which there are `< k`, so a free colour remains.  (No chordality is required for this bound.)
-/

/-
Under a PEO, a vertex together with its earlier neighbours forms a clique.
-/

/-
Under a PEO, `earlierDegree v + 1 ≤ ω(G)`: the earlier-neighbour count of every vertex is
bounded by the clique number.
-/

/-
**Linear-scan optimality for chordal graphs.**  A graph with a perfect elimination
ordering is colourable with `ω(G)` colours.
-/

/-
**Chordal graphs are perfect.**  If `G` has a perfect elimination ordering then its
chromatic number equals its clique number.  For register allocation this says: the optimal
number of registers for an SSA program equals the maximum number of simultaneously live
variables, and greedy colouring along the elimination order attains it.
-/

/-! ## Interval graphs as a special case of chordal graphs -/






/-
**Interval graphs are chordal.**  When live ranges are enumerated in increasing order of
their start points (`Monotone lo`), the interval interference graph has a perfect elimination
ordering: the earlier neighbours of a variable are all live at its start point, hence pairwise
overlap.  (Well-formedness `lo ≤ hi` of the ranges is not even needed for chordality.)
-/




open ChordalRegAlloc in
theorem solution(G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : ∀ v, (earlierNeighbours G v).card < k) : G.Colorable k := by
  -- Define a coloring function based on the elimination order.
  have hcolor : ∃ c : Fin n → Fin k, ∀ v : Fin n, ∀ w ∈ earlierNeighbours G v, c v ≠ c w := by
    rcases n with ( _ | n ) <;> simp_all +decide;
    -- By induction on $n$, we can color the vertices in such a way that no two adjacent vertices share the same color.
    have h_ind : ∀ (s : Finset (Fin (n + 1))), ∃ c : Fin (n + 1) → Fin k, ∀ v ∈ s, ∀ w ∈ s, w < v → G.Adj v w → ¬c v = c w := by
      intro s
      induction' s using Finset.strongInduction with s ih;
      by_cases hs : s.Nonempty;
      · obtain ⟨m, hm⟩ : ∃ m ∈ s, ∀ v ∈ s, v ≤ m := by
          exact ⟨ Finset.max' s hs, Finset.max'_mem s hs, fun v hv => Finset.le_max' s v hv ⟩;
        obtain ⟨ c, hc ⟩ := ih ( s.erase m ) ( Finset.erase_ssubset hm.1 );
        -- Let $N$ be the set of earlier neighbors of $m$.
        set N := earlierNeighbours G m;
        -- Since $N$ is a subset of $s.erase m$, we can use the induction hypothesis to color $N$.
        obtain ⟨cv, hcv⟩ : ∃ cv : Fin k, cv ∉ N.image c := by
          contrapose! hk;
          exact ⟨ m, by simpa using Finset.card_le_card ( show Finset.univ ⊆ Finset.image c N from fun x _ => hk x ) |> le_trans <| Finset.card_image_le ⟩;
        use fun v => if v = m then cv else c v
        intro v hv w hw hlt hadj
        by_cases hvm : v = m
        · subst v
          by_cases hwm : w = m
          · subst w
            exfalso
            exact (lt_irrefl _) hlt
          · show ¬((if m = m then cv else c m) = (if w = m then cv else c w))
            rw [if_pos rfl, if_neg hwm]
            have hwN : w ∈ N := by
              simpa [N, mem_earlierNeighbours] using ⟨hlt, hadj⟩
            exact fun h : cv = c w => hcv (Finset.mem_image.mpr ⟨w, hwN, h.symm⟩)
        · by_cases hwm : w = m
          · subst w
            exfalso
            exact (not_lt_of_ge (hm.2 v hv)) hlt
          · have hne : ¬ c v = c w :=
              hc v (by simpa using ⟨hvm, hv⟩) w (by simpa using ⟨hwm, hw⟩) hlt hadj
            simpa [hvm, hwm] using hne
      · exact ⟨ fun _ => ⟨ 0, by linarith [ hk 0 ] ⟩, by aesop ⟩;
    exact Exists.elim ( h_ind Finset.univ ) fun c hc => ⟨ c, fun v w hv hw => hc v ( Finset.mem_univ v ) w ( Finset.mem_univ w ) hv hw ⟩;
  obtain ⟨c, hc⟩ := hcolor
  use fun v => c v
  intro v w hvw
  by_cases hvw' : v < w;
  · exact hc _ _ ( by rw [ SimpleGraph.adj_comm ] at hvw; aesop ) |> Ne.symm;
  · exact hc v w ( by rw [ mem_earlierNeighbours ] ; exact ⟨ lt_of_le_of_ne ( le_of_not_gt hvw' ) ( by aesop ), hvw ⟩ )
