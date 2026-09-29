-- Prove2me | solution 1 for KServer.lazy_schedule
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:49:00.726156+00:00
-- url     : https://prove2.me/submissions/2a4b9e4d-bec4-4313-866a-7aef06647f6b

import Mathlib
import Definitions.Def_KServer_model

open KServer

private theorem moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

/-- **Every offline schedule can be made lazy without increasing its cost.**  A lazy
schedule serves each request by moving a single server directly onto it. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M)
    (S : ℕ → Config k M) (hS : ServesFrom C₀ σ S) :
    ∃ S' : ℕ → Config k M, ServesFrom C₀ σ S' ∧
      (∀ j : Fin σ.length, ∃ i : Fin k, S' (j + 1) = Function.update (S' j) i (σ.get j)) ∧
      (∑ j ∈ Finset.range σ.length, moveCost (S' j) (S' (j + 1)))
          + moveCost (S' σ.length) X
        ≤ (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) X := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  set d₀ : M := C₀ ⟨0, hk0⟩ with hd₀
  -- for each step, the index that `S` puts on the request
  have hidx : ∀ j : ℕ, ∃ i : Fin k, ∀ hj : j < σ.length, S (j + 1) i = σ.getD j d₀ := by
    intro j
    by_cases hj : j < σ.length
    · obtain ⟨i, hi⟩ := hS.2 ⟨j, hj⟩
      refine ⟨i, fun _ => ?_⟩
      rw [hi, List.getD_eq_getElem σ _ hj]
      simp
    · exact ⟨⟨0, hk0⟩, fun h => absurd h hj⟩
  choose idx hidx using hidx
  -- the lazy schedule
  set S' : ℕ → Config k M := fun j =>
    Nat.rec C₀ (fun m prev => Function.update prev (idx m) (σ.getD m d₀)) j with hS'def
  have hS'0 : S' 0 = C₀ := rfl
  have hS'succ : ∀ j : ℕ, S' (j + 1) = Function.update (S' j) (idx j) (σ.getD j d₀) :=
    fun _ => rfl
  have hlazy : ∀ j : Fin σ.length,
      ∃ i : Fin k, S' (j + 1) = Function.update (S' j) i (σ.get j) := by
    intro j
    refine ⟨idx j, ?_⟩
    rw [hS'succ, List.getD_eq_getElem σ _ j.2]
    simp
  have hserves : ServesFrom C₀ σ S' := by
    refine ⟨hS'0, ?_⟩
    intro j
    refine ⟨idx j, ?_⟩
    rw [hS'succ, Function.update_self, List.getD_eq_getElem σ _ j.2]
    simp
  refine ⟨S', hserves, hlazy, ?_⟩
  -- the potential: the distance from the lazy schedule to the original one
  set Φ : ℕ → ℝ := fun j => moveCost (S' j) (S j) with hΦdef
  have hstep : ∀ j : ℕ, j < σ.length →
      moveCost (S' j) (S' (j + 1)) + Φ (j + 1) ≤ Φ j + moveCost (S j) (S (j + 1)) := by
    intro j hj
    have hSi : S (j + 1) (idx j) = σ.getD j d₀ := hidx j hj
    have hL : moveCost (S' j) (S' (j + 1)) + Φ (j + 1)
        = ∑ l, (dist (S' j l) (S' (j + 1) l) + dist (S' (j + 1) l) (S (j + 1) l)) := by
      rw [hΦdef]
      simp only [moveCost, ← Finset.sum_add_distrib]
    have hR : Φ j + moveCost (S j) (S (j + 1))
        = ∑ l, (dist (S' j l) (S j l) + dist (S j l) (S (j + 1) l)) := by
      rw [hΦdef]
      simp only [moveCost, ← Finset.sum_add_distrib]
    rw [hL, hR]
    refine Finset.sum_le_sum fun l _ => ?_
    by_cases hl : l = idx j
    · rw [hS'succ, hl, Function.update_self, hSi, dist_self, add_zero]
      exact dist_triangle _ _ _
    · rw [hS'succ, Function.update_of_ne hl, dist_self, zero_add]
      exact dist_triangle _ _ _
  -- telescope
  have hsum : (∑ j ∈ Finset.range σ.length, moveCost (S' j) (S' (j + 1))) + Φ σ.length
      ≤ Φ 0 + ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
    have key : ∀ n : ℕ, n ≤ σ.length →
        (∑ j ∈ Finset.range n, moveCost (S' j) (S' (j + 1))) + Φ n
          ≤ Φ 0 + ∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1)) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
          intro hn
          have h1 := ih (by omega)
          have h2 := hstep n (by omega)
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          linarith
    exact key σ.length le_rfl
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦdef]
    simp only []
    rw [hS'0, hS.1, moveCost]
    simp
  have hfin : moveCost (S' σ.length) X ≤ Φ σ.length + moveCost (S σ.length) X := by
    rw [hΦdef]
    exact moveCost_triangle _ _ _
  linarith
