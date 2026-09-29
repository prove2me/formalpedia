-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.sum_two_mul_card_edgeFinset_cutSubgraph
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:24:20.299643+00:00
-- url     : https://prove2.me/submissions/0f41b734-9e5b-46e7-a08f-71e62c8337df

import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
open Catalog.Combinatorics.BipartiteExtremalTrees Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ c : V → Bool, 2 * #(cutSubgraph G c).edgeFinset
      = 2 ^ (Fintype.card V) * #G.edgeFinset := by
  classical
  -- flipping `c` at `v` swaps "cut" and "uncut" colourings of the pair `v, w`
  have hcount : ∀ v w : V, v ≠ w →
      2 * (univ.filter (fun c : V → Bool => c v ≠ c w)).card = 2 ^ Fintype.card V := by
    intro v w hvw
    have hswap : (univ.filter (fun c : V → Bool => c v ≠ c w)).card
        = (univ.filter (fun c : V → Bool => ¬ c v ≠ c w)).card := by
      apply card_nbij' (fun c => Function.update c v (!c v)) (fun c => Function.update c v (!c v))
      · intro c hc
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hc ⊢
        rw [Function.update_self, Function.update_of_ne hvw.symm]
        cases h1 : c v <;> cases h2 : c w <;> simp_all
      · intro c hc
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hc ⊢
        rw [Function.update_self, Function.update_of_ne hvw.symm]
        cases h1 : c v <;> cases h2 : c w <;> simp_all
      · intro c _
        simp
      · intro c _
        simp
    have htot := card_filter_add_card_filter_not (s := (univ : Finset (V → Bool)))
      (fun c : V → Bool => c v ≠ c w)
    rw [card_univ, Fintype.card_fun, Fintype.card_bool] at htot
    omega
  -- `2 |E(cut c)|` is the sum of cut-degrees
  have hdeg : ∀ c : V → Bool, 2 * #(cutSubgraph G c).edgeFinset
      = ∑ v, ∑ w, if G.Adj v w ∧ c v ≠ c w then 1 else 0 := by
    intro c
    rw [← (cutSubgraph G c).sum_degrees_eq_twice_card_edges]
    refine sum_congr rfl fun v _ => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree, sum_boole]
    congr 1
    ext w
    simp [cutSubgraph]
  -- swap the order of summation and count colourings per ordered edge
  have hswapsum : 2 * ∑ c : V → Bool, 2 * #(cutSubgraph G c).edgeFinset
      = ∑ v, ∑ w, if G.Adj v w then 2 ^ Fintype.card V else 0 := by
    rw [sum_congr rfl (fun c _ => hdeg c), sum_comm, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    by_cases hadj : G.Adj v w
    · rw [if_pos hadj, ← hcount v w (G.ne_of_adj hadj)]
      simp only [hadj, true_and]
      rw [sum_boole]
      rfl
    · rw [if_neg hadj]
      simp [hadj]
  have hrhs : ∑ v, ∑ w, (if G.Adj v w then 2 ^ Fintype.card V else 0)
      = 2 ^ Fintype.card V * (2 * #G.edgeFinset) := by
    rw [← G.sum_degrees_eq_twice_card_edges, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← sum_filter, sum_const, smul_eq_mul, mul_comm]
    congr 2
    ext w
    simp
  rw [hrhs] at hswapsum
  have : 2 * ∑ c : V → Bool, 2 * #(cutSubgraph G c).edgeFinset
      = 2 * (2 ^ Fintype.card V * #G.edgeFinset) := by rw [hswapsum]; ring
  omega
