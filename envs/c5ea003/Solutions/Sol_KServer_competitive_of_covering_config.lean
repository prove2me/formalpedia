-- Prove2me | solution 1 for KServer.competitive_of_covering_config
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:35:55.844725+00:00
-- url     : https://prove2.me/submissions/5c8a9e11-6f06-4ac4-9ced-ac316aa5b1b8

import Mathlib
import Definitions.Def_KServer_model

open KServer

private theorem moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

/-- If some configuration covers every point of the space, the servers can be parked there
once and for all: the resulting algorithm has bounded total cost, hence is `c`-competitive
for every `c ≥ 0`. -/
theorem solution (k : ℕ) (M : Type) [MetricSpace M] (C₀ Y : Config k M)
    (hY : ∀ x : M, ∃ i, Y i = x) (c : ℝ) (hc : 0 ≤ c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A c := by
  classical
  set conf : List M → Config k M := fun l => if l = [] then C₀ else Y with hconfdef
  have hconf_nil : conf [] = C₀ := by simp [hconfdef]
  have hconf_ne : ∀ l : List M, l ≠ [] → conf l = Y := by
    intro l hl; simp [hconfdef, hl]
  have hserves : ∀ (l : List M) (r : M), ∃ i, conf (l ++ [r]) i = r := by
    intro l r
    rw [hconf_ne _ (by simp)]
    exact hY r
  refine ⟨⟨conf, hserves⟩, hconf_nil, ⟨moveCost C₀ Y, fun σ => ?_⟩⟩
  set n := σ.length with hn
  have hlen : ∀ t : ℕ, t ≤ n → (σ.take t).length = t := by
    intro t ht; rw [List.length_take]; omega
  have hterm : ∀ t ∈ Finset.range n,
      moveCost (conf (σ.take t)) (conf (σ.take (t + 1)))
        ≤ (if t = 0 then moveCost C₀ Y else 0) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    have hne1 : σ.take (t + 1) ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [hlen (t + 1) (by omega)] at this
      simp at this
    rw [hconf_ne _ hne1]
    by_cases ht0 : t = 0
    · subst ht0
      rw [List.take_zero, hconf_nil, if_pos rfl]
    · have hne0 : σ.take t ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [hlen t (by omega)] at this
        exact ht0 this
      rw [hconf_ne _ hne0, if_neg ht0, moveCost_self]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_ite_eq' (Finset.range n) 0 (fun _ => moveCost C₀ Y)] at hsum
  have hmc : (0:ℝ) ≤ moveCost C₀ Y := moveCost_nonneg _ _
  have hsplit : (if (0:ℕ) ∈ Finset.range n then moveCost C₀ Y else 0) ≤ moveCost C₀ Y := by
    split <;> linarith
  have hcost : (⟨conf, hserves⟩ : OnlineAlgorithm k M).cost σ ≤ moveCost C₀ Y := by
    calc (⟨conf, hserves⟩ : OnlineAlgorithm k M).cost σ
        = ∑ t ∈ Finset.range n, moveCost (conf (σ.take t)) (conf (σ.take (t + 1))) := rfl
      _ ≤ _ := hsum
      _ ≤ moveCost C₀ Y := hsplit
  have hoff : (0:ℝ) ≤ offlineCost ((⟨conf, hserves⟩ : OnlineAlgorithm k M).conf []) σ := by
    unfold offlineCost
    refine Real.sInf_nonneg ?_
    rintro z ⟨S, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  nlinarith [hcost, hoff, hc]
