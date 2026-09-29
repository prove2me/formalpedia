-- Prove2me | solution 1 for KServer.workFn_step_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:18:13.877056+00:00
-- url     : https://prove2.me/submissions/77cdfd7e-91a5-41f2-96cc-c6ac0b032839

import Mathlib
import Definitions.Def_KServer_workfunction

open KServer

private theorem moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem moveCost_comm {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    moveCost A B = moveCost B A := by
  unfold moveCost; exact Finset.sum_congr rfl fun i _ => dist_comm _ _

private theorem sched_exists (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private def Wset {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem workFn_eq {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (Wset C₀ σ X) := rfl

private theorem Wset_nonempty (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : (Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sched_exists k hk M C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem Wset_bdd {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : BddBelow (Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  have h2 := moveCost_nonneg (S σ.length) X
  linarith

/-- A schedule for `σ ++ [r]` is in particular a schedule for `σ`. -/
private theorem serves_of_serves_append {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (S : ℕ → Config k M)
    (hS : ServesFrom C₀ (σ ++ [r]) S) : ServesFrom C₀ σ S := by
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  refine ⟨hS.1, ?_⟩
  intro j
  obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
  exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩

/-- **One step of the work-function recurrence, lower half.**  Up to any `ε > 0`, the new
work function at `Z` is attained by some configuration `Y` covering the new request. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Z : Config k M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : Config k M, (∃ i, Y i = r) ∧
      workFn C₀ σ Y + moveCost Y Z ≤ workFn C₀ (σ ++ [r]) Z + ε := by
  classical
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  have hlt : sInf (Wset C₀ (σ ++ [r]) Z) < workFn C₀ (σ ++ [r]) Z + ε := by
    rw [workFn_eq]; linarith
  obtain ⟨c, hcT, hclt⟩ :=
    exists_lt_of_csInf_lt (Wset_nonempty k hk M C₀ (σ ++ [r]) Z) hlt
  obtain ⟨S, hS, rfl⟩ := hcT
  refine ⟨S (n + 1), ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hS.2 ⟨n, by rw [hlen]; omega⟩
    refine ⟨i, ?_⟩
    rw [hi]
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right (by omega)]
    simp [hn]
  · have hmem : (∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1)))
        + moveCost (S n) (S (n + 1)) ∈ Wset C₀ σ (S (n + 1)) :=
      ⟨S, serves_of_serves_append C₀ σ r S hS, by rw [← hn]⟩
    have h1 := csInf_le (Wset_bdd C₀ σ (S (n + 1))) hmem
    rw [← workFn_eq] at h1
    rw [hlen, Finset.sum_range_succ] at hclt
    linarith
