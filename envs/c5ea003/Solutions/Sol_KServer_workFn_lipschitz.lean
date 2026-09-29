-- Prove2me | solution 1 for KServer.workFn_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T05:19:48.507298+00:00
-- url     : https://prove2.me/submissions/f37557ef-bb52-4849-b01b-833228877545

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

/-- Nonnegativity. -/
private theorem wf_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by
  rw [workFn_eq]
  refine le_csInf (Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  have h2 := moveCost_nonneg (S σ.length) X
  linarith

/-- Work-function values stay within the distance of their configurations. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by
  rw [workFn_eq, workFn_eq]
  have hkey : ∀ c ∈ Wset C₀ σ Y, sInf (Wset C₀ σ X) - moveCost Y X ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X ∈ Wset C₀ σ X := ⟨S, hS, rfl⟩
    have h1 := csInf_le (Wset_bdd C₀ σ X) hmem
    have h2 := moveCost_triangle (S σ.length) Y X
    linarith
  have := le_csInf (Wset_nonempty k hk M C₀ σ Y) hkey
  linarith
