-- Prove2me | solution 1 for KServer.finite_game_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T15:21:28.872187+00:00
-- url     : https://prove2.me/submissions/d5e46bd6-81a8-41a5-a79f-a5d5b83fa0a3

import Definitions.Def_KServer_finite_game
import Theorems.Thm_KServer_exists_lazy_algorithm

set_option autoImplicit false
open KServer

private theorem game_stop {k : ℕ} (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    (P : Finset M) (b : List M → ℝ) (n : ℕ) (l : List M) (C : Config k M) :
    -b l ≤ finiteGameValue hk P b n l C := by
  classical
  cases n with
  | zero => exact le_rfl
  | succ n =>
    simp only [finiteGameValue]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl

private theorem game_step {k : ℕ} (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    (P : Finset M) (b : List M → ℝ) (n : ℕ) (l : List M) (C : Config k M)
    (r : M) (hr : r ∈ P) :
    ∃ i : Fin k, dist (C i) r +
      finiteGameValue hk P b n (l ++ [r]) (Function.update C i r) ≤
        finiteGameValue hk P b (n + 1) l C := by
  classical
  have hP : P.Nonempty := ⟨r, hr⟩
  let f (r : M) : ℝ := Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    (fun i => dist (C i) r + finiteGameValue hk P b n (l ++ [r])
      (Function.update C i r))
  have heq : finiteGameValue hk P b (n + 1) l C = max (-b l) (P.sup' hP f) := by
    simp [finiteGameValue, f, hP]
  have hle : f r ≤ finiteGameValue hk P b (n + 1) l C := by
    rw [heq]
    exact (Finset.le_sup' f hr).trans (le_max_right _ _)
  obtain ⟨i, _, hi⟩ := (Finset.inf'_le_iff _).mp hle
  exact ⟨i, hi⟩

/-- Cost splitting copied from Shuze Chen's accepted laziness proof,
submission 8eef28a0-5266-4db7-886c-ab1fdc1f5d07. -/
private theorem cost_concat {k : ℕ} {M : Type} [MetricSpace M]
    (X : OnlineAlgorithm k M) (l : List M) (r : M) :
    X.cost (l ++ [r]) = X.cost l + moveCost (X.conf l) (X.conf (l ++ [r])) := by
  unfold OnlineAlgorithm.cost
  have hlen : (l ++ [r]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

private theorem move_update {k : ℕ} {M : Type} [MetricSpace M]
    (C : Config k M) (i : Fin k) (r : M) :
    moveCost C (Function.update C i r) = dist (C i) r := by
  classical
  unfold moveCost
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [Function.update_of_ne hji]) (by simp)]
  simp

/-- Backward induction synthesizes one total online algorithm attaining the
finite-game value simultaneously on every allowed prefix. -/
private theorem game_synthesis (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (P : Finset M) (b : List M → ℝ) (n : ℕ) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
      (∀ (l : List M) (r : M), ∃ i : Fin k,
        A.conf (l ++ [r]) = Function.update (A.conf l) i r) ∧
      ∀ σ : List M, σ.length ≤ n → (∀ r ∈ σ, r ∈ P) →
        A.cost σ ≤ b σ + finiteGameValue hk P b n [] C₀ := by
  classical
  let idx (l : List M) (C : Config k M) (r : M) : Fin k :=
    if hr : r ∈ P then (game_step hk P b (n - (l.length + 1)) l C r hr).choose
    else ⟨0, hk⟩
  let conf : List M → Config k M := fun l =>
    List.reverseRecOn l C₀ (fun l r C => Function.update C (idx l C r) r)
  have hnil : conf [] = C₀ := by simp [conf]
  have hstep (l : List M) (r : M) :
      conf (l ++ [r]) = Function.update (conf l) (idx l (conf l) r) r := by
    simp [conf]
  let A : OnlineAlgorithm k M :=
    ⟨conf, fun l r => ⟨idx l (conf l) r, by rw [hstep]; simp⟩⟩
  have hpot (l : List M) (hl : l.length ≤ n) (hP : ∀ r ∈ l, r ∈ P) :
      A.cost l + finiteGameValue hk P b (n - l.length) l (conf l) ≤
        finiteGameValue hk P b n [] C₀ := by
    induction l using List.reverseRecOn with
    | nil => simpa [A, OnlineAlgorithm.cost, hnil]
    | append_singleton l r ih =>
      have hlen : l.length + 1 ≤ n := by simpa using hl
      have hr : r ∈ P := hP r (by simp)
      have hprev := ih (by omega) (fun s hs => hP s (List.mem_append_left _ hs))
      have hg := (game_step hk P b (n - (l.length + 1)) l (conf l) r hr).choose_spec
      have hi : idx l (conf l) r =
          (game_step hk P b (n - (l.length + 1)) l (conf l) r hr).choose := by
        simp [idx, hr]
      rw [← hi, ← hstep] at hg
      have hbudget : n - (l.length + 1) + 1 = n - l.length := by omega
      rw [hbudget] at hg
      rw [cost_concat]
      change A.cost l + moveCost (conf l) (conf (l ++ [r])) + _ ≤ _
      rw [hstep, move_update]
      rw [hstep] at hg
      simp only [List.length_append, List.length_singleton]
      linarith
  refine ⟨A, hnil, fun l r => ⟨idx l (conf l) r, hstep l r⟩, ?_⟩
  intro σ hσ hP
  have hp := hpot σ hσ hP
  have hs := game_stop hk P b (n - σ.length) σ (conf σ)
  linarith



/-- The game value is also a lower bound for every lazy algorithm. -/
private theorem game_lower {k : ℕ} (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    (P : Finset M) (b : List M → ℝ) (A : OnlineAlgorithm k M)
    (hA : ∀ (l : List M) (r : M), ∃ i : Fin k,
      A.conf (l ++ [r]) = Function.update (A.conf l) i r)
    (a : ℝ) (n : ℕ) (l : List M)
    (h : ∀ σ : List M, σ.length ≤ n → (∀ r ∈ σ, r ∈ P) →
      A.cost (l ++ σ) ≤ b (l ++ σ) + a) :
    finiteGameValue hk P b n l (A.conf l) ≤ a - A.cost l := by
  classical
  induction n generalizing l with
  | zero =>
    have hh := h [] (by simp) (by simp)
    simp only [List.append_nil] at hh
    change -b l ≤ a - A.cost l
    linarith
  | succ n ih =>
    have hs : -b l ≤ a - A.cost l := by
      have hh := h [] (by simp) (by simp)
      simp only [List.append_nil] at hh
      linarith
    change (if hP : P.Nonempty then max (-b l)
      (P.sup' hP (fun r => Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        (fun i => dist (A.conf l i) r + finiteGameValue hk P b n (l ++ [r])
          (Function.update (A.conf l) i r)))) else -b l) ≤ _
    split_ifs with hP
    · apply max_le hs
      apply Finset.sup'_le
      intro r hr
      obtain ⟨i, hi⟩ := hA l r
      apply (Finset.inf'_le _ (Finset.mem_univ i)).trans
      have hh := ih (l ++ [r]) (by
        intro σ hσ hσP
        have hh := h (r :: σ) (by simpa using Nat.succ_le_succ hσ)
          (by intro s hs; rcases List.mem_cons.mp hs with hs | hs
              · simpa [hs] using hr
              · exact hσP s hs)
        simpa [List.append_assoc] using hh)
      rw [cost_concat, hi, move_update] at hh
      linarith
    · exact hs

/-- Exact backward induction for finite request sets. This includes synthesis
of a total algorithm and the converse via the proved laziness reduction. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (P : Finset M) (b : List M → ℝ) (n : ℕ) (a : ℝ) :
    finiteGameValue hk P b n [] C₀ ≤ a ↔
      ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
        ∀ σ : List M, σ.length ≤ n → (∀ r ∈ σ, r ∈ P) →
          A.cost σ ≤ b σ + a := by
  constructor
  · intro hv
    obtain ⟨A, hA0, _, hA⟩ := game_synthesis k hk M C₀ P b n
    exact ⟨A, hA0, fun σ hσ hP => (hA σ hσ hP).trans (add_le_add_right hv _)⟩
  · rintro ⟨A, hA0, hA⟩
    obtain ⟨B, hB0, hBA, hB⟩ := KServer.exists_lazy_algorithm k M A
    have hh := game_lower hk P b B hB a n [] (by
      intro σ hσ hP
      simpa using (hBA σ).trans (hA σ hσ hP))
    simpa [hB0, hA0, OnlineAlgorithm.cost] using hh

#print axioms solution
