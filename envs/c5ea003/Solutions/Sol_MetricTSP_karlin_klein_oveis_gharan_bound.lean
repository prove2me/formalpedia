-- Prove2me | solution 1 for MetricTSP.karlin_klein_oveis_gharan_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T19:42:42.491606+00:00
-- url     : https://prove2.me/submissions/6f84be2b-e780-4583-9c10-89a9b1f805ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost
import Theorems.Thm_MetricTSP_kkg_connected_graph_and_join
import Theorems.Thm_MetricTSP_fractional_join_pairing
import Theorems.Thm_MetricTSP_tour_of_parity_join
import Theorems.Thm_MetricTSP_tsp_opt_le_tour_cost
import Theorems.Thm_MetricTSP_tour_vector_held_karp

open MetricTSP

/-- Metric costs are nonnegative: `0 = c u u ≤ c u v + c v u = 2 c u v`. -/
private lemma metric_cost_nonneg {n : ℕ} {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c)
    (u v : Fin n) : 0 ≤ c u v := by
  obtain ⟨hs, hd, ht⟩ := hc
  have := ht u v u
  rw [hd u, hs v u] at this
  linarith

/-- The Held–Karp objective of a feasible point is nonnegative for metric costs. -/
private lemma lp_objective_nonneg {n : ℕ} {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c)
    {x : Fin n → Fin n → ℝ} (hx : IsHeldKarp x) :
    0 ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by
  have hxnn := hx.2.2.1
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => ?_)
  exact mul_nonneg (metric_cost_nonneg hc u v) (hxnn u v)

theorem solution :
    ∃ ε : ℝ, 1 / 10 ^ 36 < ε ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ c : Fin n → Fin n → ℝ, IsMetricCost c →
        tspOpt c ≤ (3 / 2 - ε) * hkValue c := by
  obtain ⟨ε, hε, hA⟩ := kkg_connected_graph_and_join
  -- Cap ε at 1 so that the factor `3/2 - ε` stays positive.
  refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
  intro n hn c hc
  have hle : min ε 1 ≤ ε := min_le_left ε 1
  have hpos : 0 < 3 / 2 - min ε 1 := by have := min_le_right ε 1; linarith
  -- Pointwise bound: a tour within `3/2 - ε` of every feasible LP point.
  have key : ∀ x, IsHeldKarp x →
      tspOpt c ≤ (3 / 2 - min ε 1) * ((1 / 2) * ∑ u, ∑ v, c u v * x u v) := by
    intro x hx
    classical
    obtain ⟨G, y, hG, hsym, hnn, hcut, hcost⟩ := hA n hn c hc x hx
    set T : Finset (Fin n) := Finset.univ.filter fun v => Odd (G.degree v) with hTdef
    have hTeven : Even T.card := G.even_card_odd_degree_vertices
    have hcutT : ∀ S : Finset (Fin n), Odd (S ∩ T).card →
        1 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, y u v := by
      intro S hS
      apply hcut
      convert hS using 2
      ext v
      simp [hTdef]
    obtain ⟨f, hfT, hfout, hfcost⟩ := fractional_join_pairing n c hc T hTeven y hsym hnn hcutT
    have hinv : ∀ v, f (f v) = v := by
      intro v
      by_cases hv : v ∈ T
      · exact (hfT v hv).2.1
      · rw [hfout v hv, hfout v hv]
    have hodd : ∀ v, f v ≠ v ↔ Odd (G.degree v) := by
      intro v
      constructor
      · intro h
        by_contra hv
        exact h (hfout v (by simpa [hTdef] using hv))
      · intro h
        exact (hfT v (by simpa [hTdef] using h)).2.2
    obtain ⟨π, hπ⟩ := tour_of_parity_join n hn c hc G hG f hinv hodd
    have hsum : ∑ v, c v (f v) = ∑ v ∈ T, c v (f v) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro v _ hv
      rw [hfout v hv, hc.2.1 v]
    calc tspOpt c ≤ tourCost c π := tsp_opt_le_tour_cost n c hc π
      _ ≤ graphCost c G + 1 / 2 * ∑ v, c v (f v) := hπ
      _ ≤ graphCost c G + 1 / 2 * ∑ u, ∑ v, c u v * y u v := by rw [hsum]; linarith
      _ ≤ (3 / 2 - ε) * ((1 / 2) * ∑ u, ∑ v, c u v * x u v) := hcost
      _ ≤ (3 / 2 - min ε 1) * ((1 / 2) * ∑ u, ∑ v, c u v * x u v) :=
        mul_le_mul_of_nonneg_right (by linarith) (lp_objective_nonneg hc hx)
  -- Pass to the infimum: the feasible set is nonempty (any tour vector lies in it).
  have hne : {t : ℝ | ∃ x : Fin n → Fin n → ℝ, IsHeldKarp x ∧
      t = (1 / 2) * ∑ u, ∑ v, c u v * x u v}.Nonempty :=
    ⟨_, tourVec (1 : Equiv.Perm (Fin n)), tour_vector_held_karp n hn 1, rfl⟩
  have hinf : tspOpt c / (3 / 2 - min ε 1) ≤ hkValue c := by
    apply le_csInf hne
    rintro t ⟨x, hx, rfl⟩
    rw [div_le_iff₀ hpos, mul_comm]
    exact key x hx
  rw [div_le_iff₀ hpos, mul_comm] at hinf
  exact hinf
