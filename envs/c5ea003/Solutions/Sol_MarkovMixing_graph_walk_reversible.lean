-- Prove2me | solution 1 for MarkovMixing.graph_walk_reversible
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:09:51.551295+00:00
-- url     : https://prove2.me/submissions/387d9365-f3ec-4a35-9b8f-fd074f6b4681

import Definitions.Def_mm_basic

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ x : V, 0 < G.degree x) :
    IsStochastic (graphWalk G) ∧
    DetailedBalance (graphWalk G)
      (fun x => (G.degree x : ℝ) / (2 * G.edgeFinset.card)) ∧
    IsStationary (graphWalk G)
      (fun x => (G.degree x : ℝ) / (2 * G.edgeFinset.card)) := by
  have hdR : ∀ x : V, (0 : ℝ) < (G.degree x : ℝ) := fun x => by exact_mod_cast hdeg x
  have hsum : ∑ x : V, (G.degree x : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    have h := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hE : (0 : ℝ) < 2 * (G.edgeFinset.card : ℝ) := by
    rw [← hsum]; exact Finset.sum_pos (fun x _ => hdR x) Finset.univ_nonempty
  have hrow : ∀ x : V, ∑ y, graphWalk G x y = 1 := by
    intro x
    have h : ∑ y, graphWalk G x y
        = ∑ _y ∈ Finset.univ.filter (G.Adj x), ((G.degree x : ℝ))⁻¹ := by
      rw [Finset.sum_filter]; rfl
    rw [h, Finset.sum_const, ← SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
    exact mul_inv_cancel₀ (hdR x).ne'
  have hstoch : IsStochastic (graphWalk G) := by
    refine ⟨fun x y => ?_, hrow⟩
    by_cases h : G.Adj x y <;> simp [graphWalk, h]
  have hdb : DetailedBalance (graphWalk G)
      (fun x => (G.degree x : ℝ) / (2 * G.edgeFinset.card)) := by
    intro x y
    show (G.degree x : ℝ) / (2 * G.edgeFinset.card) * graphWalk G x y
        = (G.degree y : ℝ) / (2 * G.edgeFinset.card) * graphWalk G y x
    by_cases h : G.Adj x y
    · show (G.degree x : ℝ) / (2 * G.edgeFinset.card)
          * (if G.Adj x y then ((G.degree x : ℝ))⁻¹ else 0)
        = (G.degree y : ℝ) / (2 * G.edgeFinset.card)
          * (if G.Adj y x then ((G.degree y : ℝ))⁻¹ else 0)
      rw [if_pos h, if_pos h.symm, div_mul_eq_mul_div, div_mul_eq_mul_div,
        mul_inv_cancel₀ (hdR x).ne', mul_inv_cancel₀ (hdR y).ne']
    · have h' : ¬ G.Adj y x := fun hc => h hc.symm
      show (G.degree x : ℝ) / (2 * G.edgeFinset.card)
          * (if G.Adj x y then ((G.degree x : ℝ))⁻¹ else 0)
        = (G.degree y : ℝ) / (2 * G.edgeFinset.card)
          * (if G.Adj y x then ((G.degree y : ℝ))⁻¹ else 0)
      rw [if_neg h, if_neg h', mul_zero, mul_zero]
  have hdist : IsDist (fun x => (G.degree x : ℝ) / (2 * G.edgeFinset.card)) := by
    refine ⟨fun x => div_nonneg (hdR x).le hE.le, ?_⟩
    show ∑ x : V, (G.degree x : ℝ) / (2 * G.edgeFinset.card) = 1
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hsum]
    exact mul_inv_cancel₀ hE.ne'
  refine ⟨hstoch, hdb, hdist, ?_⟩
  funext x
  show ∑ y, (G.degree y : ℝ) / (2 * G.edgeFinset.card) * graphWalk G y x
      = (G.degree x : ℝ) / (2 * G.edgeFinset.card)
  rw [Finset.sum_congr rfl (fun y _ => (hdb x y).symm), ← Finset.mul_sum, hrow x, mul_one]
