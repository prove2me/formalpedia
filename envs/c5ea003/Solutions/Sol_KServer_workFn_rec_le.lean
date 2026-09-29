-- Prove2me | solution 1 for KServer.workFn_rec_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T05:19:50.01653+00:00
-- url     : https://prove2.me/submissions/8f189fed-b3e7-4bdc-86f5-3ee1c41eb39f

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
private theorem wf_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
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

/-- Serving one more request never decreases the work function. -/
private theorem wf_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  rw [workFn_eq, workFn_eq]
  refine le_csInf (Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
    exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ Wset C₀ σ X := ⟨S, hserve, rfl⟩
  have h1 := csInf_le (Wset_bdd C₀ σ X) hmem
  have h2 := moveCost_triangle (S σ.length) (S (σ.length + 1)) X
  rw [hlen, Finset.sum_range_succ]
  linarith

private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

/-- Serving a request the target configuration already covers costs nothing. -/
private theorem wf_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by
  classical
  refine le_antisymm ?_ (wf_mono k hk M C₀ σ r X)
  rw [workFn_eq, workFn_eq]
  refine csInf_le_csInf (Wset_bdd C₀ (σ ++ [r]) X) (Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  set S' : ℕ → Config k M := fun j => if j = n + 1 then X else S j with hS'def
  have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
    intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
  have hS'top : S' (n + 1) = X := by rw [hS'def]; simp
  have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
    refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
    intro j
    have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
    by_cases hjn : (j : ℕ) = n
    · obtain ⟨i0, hi0⟩ := hX
      refine ⟨i0, ?_⟩
      rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hi0]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hjn, hn]
    · obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by omega⟩
      refine ⟨i, ?_⟩
      rw [hS'ne _ (by omega), hi]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by omega)]
  refine ⟨S', hserves, ?_⟩
  rw [hlen, Finset.sum_range_succ]
  have e1 : ∀ j ∈ Finset.range n,
      moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hS'ne _ (by omega), hS'ne _ (by omega)]
  rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, moveCost_self]
  ring

private theorem moveCost_update {k : ℕ} {M : Type} [MetricSpace M]
    (X : Config k M) (i : Fin k) (v : M) :
    moveCost (Function.update X i v) X = dist v (X i) := by
  classical
  have h := sum_diff_single (fun j => dist (Function.update X i v j) (X j))
    (fun _ => (0:ℝ)) i (fun j hj => by
      show dist (Function.update X i v j) (X j) = 0
      rw [Function.update_of_ne hj]; simp)
  simp only [Finset.sum_const_zero, sub_zero, Function.update_self] at h
  simpa [moveCost] using h

/-- One direction of the work-function recurrence: ending at `X` after serving `r` costs at
most what it costs to end at `X` with server `i` parked on `r`, plus that server's trip. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFn C₀ (σ ++ [r]) X ≤ workFn C₀ σ (Function.update X i r) + dist r (X i) := by
  classical
  rw [workFn_eq, workFn_eq]
  set X' : Config k M := Function.update X i r with hX'def
  have hkey : ∀ c ∈ Wset C₀ σ X', sInf (Wset C₀ (σ ++ [r]) X) - dist r (X i) ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    set n := σ.length with hn
    have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
    set S' : ℕ → Config k M := fun j => if j = n + 1 then X' else S j with hS'def
    have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
      intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
    have hS'top : S' (n + 1) = X' := by rw [hS'def]; simp
    have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
      refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
      intro j
      have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
      by_cases hjn : (j : ℕ) = n
      · refine ⟨i, ?_⟩
        rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hX'def, Function.update_self]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (by omega)]
        simp [hjn, hn]
      · obtain ⟨i2, hi2⟩ := hS.2 ⟨(j : ℕ), by omega⟩
        refine ⟨i2, ?_⟩
        rw [hS'ne _ (by omega), hi2]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_left (by omega)]
    have hmem : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X ∈ Wset C₀ (σ ++ [r]) X := ⟨S', hserves, rfl⟩
    have hval : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X
        = ((∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) X')
          + dist r (X i) := by
      rw [hlen, Finset.sum_range_succ]
      have e1 : ∀ j ∈ Finset.range n,
          moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [hS'ne _ (by omega), hS'ne _ (by omega)]
      rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, hX'def, moveCost_update]
    rw [hval] at hmem
    have h1 := csInf_le (Wset_bdd C₀ (σ ++ [r]) X) hmem
    linarith
  have := le_csInf (Wset_nonempty k hk M C₀ σ X') hkey
  linarith
