-- Prove2me | solution 1 for GreedyIndependentSet.turan_bound_of_cliqueFree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:46:35.209791+00:00
-- url     : https://prove2.me/submissions/91b7492b-c483-4e54-8f75-227d7512e0c8

-- Sol generated from Bridges/CaroWeiGreedy.lean
import Mathlib
import Definitions.Def_Bridges_CaroWeiGreedy
import Theorems.Thm_GreedyIndependentSet_caro_wei_finset
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: the probabilistic Caro–Wei bound ↔ a greedy (constructive) independent set

The Caro–Wei inequality
`α(G) ≥ ∑_v 1 / (deg v + 1)`
is the textbook example of the *probabilistic method with alterations*: order the vertices
uniformly at random and keep the vertices that precede all of their neighbours; the expected
number of kept vertices is `∑_v 1/(deg v + 1)`.

This file proves the inequality **without any probability space at all**: the whole content is a
strong induction that repeatedly deletes the closed neighbourhood of a vertex of *minimum*
degree, i.e. the greedy algorithm.  This is the constructive shadow of the expectation argument,
in the exact spirit of the mission ("Erdős's existence proofs are algorithms in disguise").

Main results:

* `GreedyIndependentSet.caro_wei_finset` — the induction engine, relativised to an arbitrary
  vertex subset `t`: there is an independent `s ⊆ t` with `∑_{v ∈ t} 1/(deg_t v + 1) ≤ #s`.
* `GreedyIndependentSet.caro_wei` — `∑_v 1/(deg v + 1) ≤ α(G)`.
* `GreedyIndependentSet.card_div_maxDegree_succ_le_indepNum` — the Turán-type corollary
  `n / (Δ + 1) ≤ α(G)`.
* `GreedyIndependentSet.turan_bound_of_cliqueFree` — Turán's theorem
  `#edges ≤ (1 - 1/r) n² / 2` for `K_{r+1}`-free graphs, on an *arbitrary* finite vertex type
  and with **no divisibility hypothesis**, obtained by applying Caro–Wei to the complement and
  Sedrakyan's (Cauchy–Schwarz) inequality.

## Catalog connections
* `Bridges/TuranExplicitCount.lean` : the explicit Turán graph attains this bound.
* `Bridges/ErdosProbabilisticRamsey.lean`, `Bridges/LovaszLocalLemmaFinite.lean` : the other
  members of the probabilistic-method trio.
-/

open Finset SimpleGraph

open GreedyIndependentSet

variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]



omit [DecidableEq V] in
lemma degIn_univ (v : V) : degIn G univ v = G.degree v := by
  rw [degIn, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]





/-- **Caro–Wei inequality**: the independence number of a finite graph is at least
`∑_v 1/(deg v + 1)`.  Proved constructively, by the greedy algorithm. -/
theorem caro_wei : ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ G.indepNum := by
  obtain ⟨s, _, hind, hsum⟩ := caro_wei_finset G univ
  refine le_trans (le_of_eq ?_) (le_trans hsum ?_)
  · exact sum_congr rfl fun v _ => by rw [degIn_univ]
  · exact_mod_cast hind.card_le_indepNum



omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- A `K_{r+1}`-free graph has clique number at most `r`. -/
lemma cliqueNum_le_of_cliqueFree {r : ℕ} (h : G.CliqueFree (r + 1)) : G.cliqueNum ≤ r := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (s := s) (n := r + 1)
    (by rw [hs.card_eq]; omega)
  exact h u ⟨hs.isClique.subset hu, hcard⟩


/-! ## From greedy independence to the off-diagonal Ramsey bound `R(3, k+1) > k²`

A triangle-free graph has independent neighbourhoods, so `Δ ≤ α`; combined with the greedy bound
`n ≤ α(Δ+1)` this gives `n ≤ α(α+1)`.  Contrapositively, a graph on more than `k(k+1)` vertices
contains a triangle or an independent set of size `k+1` — a verified lower bound for the
off-diagonal Ramsey number `R(3, k+1)`, obtained with no probability at all. -/





/-! ## Lab notes: sharpness of the two bounds

Experimental data (all checked by `decide` below, on the four-vertex Turán graph
`turanGraph 4 2`, which is the 4-cycle):

| quantity                       | value | source                            |
|--------------------------------|-------|-----------------------------------|
| `#edges`                       | `4`   | `card_edges_turanGraph_four_two`  |
| Turán bound `(1-1/2)·4²/2`     | `4`   | `turan_bound_sharp_four_two`      |
| `maxDegree`                    | `2`   | `maxDegree_turanGraph_four_two`   |
| greedy bound `n/(Δ+1) = 4/3`   | `1.33`| `card_div_maxDegree_succ_le_indepNum` |
| true independence number       | `2`   | the two colour classes            |

So the Turán inequality proved above is *attained* (it is not merely an upper bound), while the
`n/(Δ+1)` corollary is strict here — the loss is exactly the convexity slack in
Cauchy–Schwarz. -/






open GreedyIndependentSet in
theorem solution{r : ℕ} (hr : 1 ≤ r) (h : G.CliqueFree (r + 1)) :
    (#G.edgeFinset : ℝ) ≤ (1 - 1 / r) * (Fintype.card V) ^ 2 / 2 := by
  classical
  set n : ℕ := Fintype.card V with hn
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    have : G.edgeFinset = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      induction e with
      | _ a b => exact this.elim a
    simp [this, hn0]
  -- the complement graph
  have hdeg : ∀ v : V, ((Gᶜ.degree v : ℝ)) = (n : ℝ) - 1 - G.degree v := by
    intro v
    have hlt : G.degree v < n := G.degree_lt_card_verts v
    have hnat : Gᶜ.degree v + G.degree v + 1 = n := by
      rw [SimpleGraph.degree_compl]; omega
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at hcast
    linarith
  have hsumdeg : ∑ v : V, ((Gᶜ.degree v : ℝ) + 1) = (n : ℝ) ^ 2 - 2 * #G.edgeFinset := by
    have hGsum : ∑ v : V, (G.degree v : ℝ) = 2 * #G.edgeFinset := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (G.sum_degrees_eq_twice_card_edges)
    calc ∑ v : V, ((Gᶜ.degree v : ℝ) + 1)
        = ∑ v : V, ((n : ℝ) - G.degree v) := by
          refine sum_congr rfl fun v _ => by rw [hdeg v]; ring
      _ = (n : ℝ) * n - ∑ v : V, (G.degree v : ℝ) := by
          rw [sum_sub_distrib, sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
      _ = (n : ℝ) ^ 2 - 2 * #G.edgeFinset := by rw [hGsum]; ring
  have hpos : ∀ v ∈ (univ : Finset V), (0 : ℝ) < (Gᶜ.degree v : ℝ) + 1 := by
    intro v _; positivity
  have hcs : ((n : ℝ)) ^ 2 / ((n : ℝ) ^ 2 - 2 * #G.edgeFinset)
      ≤ ∑ v : V, (1 : ℝ) / ((Gᶜ.degree v : ℝ) + 1) := by
    have := Finset.sq_sum_div_le_sum_sq_div (univ : Finset V) (fun _ => (1 : ℝ)) hpos
    rw [hsumdeg] at this
    simpa [Finset.card_univ, ← hn, one_pow] using this
  have hcw : ∑ v : V, (1 : ℝ) / ((Gᶜ.degree v : ℝ) + 1) ≤ (r : ℝ) := by
    refine le_trans (caro_wei Gᶜ) ?_
    have : Gᶜ.indepNum ≤ r := by
      rw [SimpleGraph.indepNum_compl]
      exact cliqueNum_le_of_cliqueFree G h
    exact_mod_cast this
  have hSpos : (0 : ℝ) < (n : ℝ) ^ 2 - 2 * #G.edgeFinset := by
    rw [← hsumdeg]
    exact sum_pos (fun v hv => hpos v hv) (by
      simpa [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff] using hnpos)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have key : ((n : ℝ)) ^ 2 ≤ (r : ℝ) * ((n : ℝ) ^ 2 - 2 * #G.edgeFinset) := by
    rw [div_le_iff₀ hSpos] at hcs
    nlinarith [le_trans hcs (mul_le_mul_of_nonneg_right hcw hSpos.le)]
  have hfin : 2 * (r : ℝ) * #G.edgeFinset ≤ ((r : ℝ) - 1) * (n : ℝ) ^ 2 := by nlinarith [key]
  have hrw : (1 - 1 / (r : ℝ)) * (n : ℝ) ^ 2 / 2 = ((r : ℝ) - 1) * (n : ℝ) ^ 2 / (2 * r) := by
    field_simp
  rw [hrw, le_div_iff₀ (by positivity)]
  nlinarith [hfin]
