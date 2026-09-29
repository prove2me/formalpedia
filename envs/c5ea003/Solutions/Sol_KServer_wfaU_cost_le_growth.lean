-- Prove2me | solution 1 for KServer.wfaU_cost_le_growth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T05:13:37.18715+00:00
-- url     : https://prove2.me/submissions/f9c1fe32-0d85-4f68-9c5d-9ce458235ca4

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_wfaU
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_offlineCost_le_workFn
import Theorems.Thm_KServer_workFn_nil

open KServer


private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem update_comp {k : ℕ} {M : Type} (X : Config k M) (i : Fin k) (r : M)
    (π : Equiv.Perm (Fin k)) :
    (Function.update X i r) ∘ (π : Equiv.Perm (Fin k))
      = Function.update (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) r := by
  classical
  funext l
  by_cases h : l = π.symm i
  · subst h
    rw [Function.comp_apply, Equiv.apply_symm_apply, Function.update_self,
      Function.update_self]
  · have h2 : (π : Equiv.Perm (Fin k)) l ≠ i := by
      intro hc; exact h (by rw [← hc]; simp)
    simp [Function.update_of_ne h, Function.update_of_ne h2]

private theorem wfU_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ (Function.update X i r)
  have h1 := wfU_le C₀ (σ ++ [r]) X π
  have h2 := workFn_rec_le k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i)
  rw [← update_comp X i r π] at h2
  have h3 : (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) = X i := by simp
  rw [h3, hπ] at h2
  linarith

private theorem wfU_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  obtain ⟨i', hi'⟩ := workFn_rec_ge k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k)))
  refine ⟨π i', ?_⟩
  have hup : Function.update (X ∘ (π : Equiv.Perm (Fin k))) i' r
      = (Function.update X (π i') r) ∘ (π : Equiv.Perm (Fin k)) := by
    rw [update_comp X (π i') r π]; simp
  rw [hup] at hi'
  have h1 := wfU_le C₀ σ (Function.update X (π i') r) π
  have h2 : (X ∘ (π : Equiv.Perm (Fin k))) i' = X (π i') := rfl
  rw [h2, hπ] at hi'
  linarith

private theorem wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine workFn_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

private theorem wfU_step_self (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (U : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) U
      = workFnU C₀ (σ ++ [r]) (Function.update U i r) + dist r (U i) := by
  classical
  obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ σ r U
  refine ⟨i, le_antisymm ?_ ?_⟩
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    have := wfU_rec_le k hk M C₀ σ r U i
    rw [← hc] at this
    exact this
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    rw [hc]
    exact hi

private theorem wfU_nil_self {k : ℕ} (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) : workFnU C₀ [] C₀ = 0 := by
  refine le_antisymm ?_ ?_
  · have h := wfU_le C₀ [] C₀ 1
    have h0 : workFn C₀ [] (C₀ ∘ (1 : Equiv.Perm (Fin k))) = 0 := by
      rw [workFn_nil k hk M C₀ (C₀ ∘ (1 : Equiv.Perm (Fin k)))]
      unfold moveCost
      simp
    rw [h0] at h
    exact h
  · refine le_ciInf fun π => ?_
    rw [workFn_nil k hk M C₀ (C₀ ∘ π)]
    exact Finset.sum_nonneg fun i _ => dist_nonneg

private theorem offlineCost_le_wfU (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    offlineCost C₀ σ ≤ workFnU C₀ σ X :=
  le_ciInf fun π => offlineCost_le_workFn k hk M C₀ σ (X ∘ π)

/-- The classical Work Function Algorithm's move is exactly what the update operator
charges to the unlabelled work function. -/
private theorem wfaU_step_eq (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (l : List M) (Cprev : Config k M) (r : M) :
    workFnU C₀ (l ++ [r]) Cprev
      = workFnU C₀ (l ++ [r]) (wfaUStep hk C₀ l Cprev r)
        + moveCost Cprev (wfaUStep hk C₀ l Cprev r) := by
  refine le_antisymm ?_ ?_
  · have h := workFnU_lipschitz k hk M C₀ (l ++ [r]) Cprev (wfaUStep hk C₀ l Cprev r)
    have hc : moveCost (wfaUStep hk C₀ l Cprev r) Cprev
        = moveCost Cprev (wfaUStep hk C₀ l Cprev r) := by
      unfold moveCost
      exact Finset.sum_congr rfl fun i _ => dist_comm _ _
    linarith [h, hc.symm ▸ h]
  · obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ l r Cprev
    have hcov : ∃ j, (Function.update Cprev i r) j = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ l r (Function.update Cprev i r) hcov
    have hmin := wfaUStep_min hk C₀ l Cprev r (Function.update Cprev i r) hcov
    have hmc : moveCost Cprev (Function.update Cprev i r) = dist r (Cprev i) := by
      unfold moveCost
      rw [Finset.sum_eq_single i]
      · rw [Function.update_self]; exact dist_comm _ _
      · intro j _ hj; rw [Function.update_of_ne hj, dist_self]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← hc] at hi
    linarith

/-- **Lemma 2 of Bein, Chrobak and Larmore for the classical WFA.** -/
theorem solution (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (σ : List M) (u : ℕ → ℝ)
    (hu : ∀ t : ℕ, t < σ.length → ∀ X : Config k M,
      workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) :
    (WFAU hk C₀).cost σ + offlineCost C₀ σ ≤ ∑ t ∈ Finset.range σ.length, u t := by
  classical
  set S : ℕ → Config k M := fun t => (WFAU hk C₀).conf (σ.take t) with hSdef
  set f : ℕ → ℝ := fun t => workFnU C₀ (σ.take t) (S t) with hfdef
  have hsplit : ∀ (t : ℕ) (ht : t < σ.length), σ.take (t + 1) = σ.take t ++ [σ[t]'ht] := by
    intro t ht
    rw [List.take_succ, List.getElem?_eq_getElem ht]
    rfl
  have hSsucc : ∀ (t : ℕ) (ht : t < σ.length),
      S (t + 1) = wfaUStep hk C₀ (σ.take t) (S t) (σ[t]'ht) := by
    intro t ht
    show (wfaUAux hk C₀ (σ.take (t + 1))).2
        = wfaUStep hk C₀ (σ.take t) ((wfaUAux hk C₀ (σ.take t)).2) (σ[t]'ht)
    rw [hsplit t ht, wfaUAux_append hk C₀ (σ.take t) (σ[t]'ht), wfaUAux_fst]
  have hstep : ∀ (t : ℕ) (ht : t < σ.length),
      workFnU C₀ (σ.take (t + 1)) (S t)
        = workFnU C₀ (σ.take (t + 1)) (S (t + 1)) + moveCost (S t) (S (t + 1)) := by
    intro t ht
    rw [hSsucc t ht]
    rw [hsplit t ht]
    exact wfaU_step_eq k hk M C₀ (σ.take t) (S t) (σ[t]'ht)
  have hbound : ∀ t ∈ Finset.range σ.length,
      moveCost (S t) (S (t + 1)) ≤ (f t + u t) - f (t + 1) := by
    intro t htm
    have ht : t < σ.length := Finset.mem_range.mp htm
    have h1 := hstep t ht
    have h2 := hu t ht (S t)
    rw [hfdef]
    simp only
    linarith
  have hcost : (WFAU hk C₀).cost σ ≤ ∑ t ∈ Finset.range σ.length, ((f t + u t) - f (t + 1)) := by
    refine le_of_eq_of_le ?_ (Finset.sum_le_sum hbound)
    rfl
  have hsplit2 : (∑ t ∈ Finset.range σ.length, ((f t + u t) - f (t + 1)))
      = (∑ t ∈ Finset.range σ.length, (f t - f (t + 1)))
        + ∑ t ∈ Finset.range σ.length, u t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have htel : (∑ t ∈ Finset.range σ.length, (f t - f (t + 1))) = f 0 - f σ.length :=
    Finset.sum_range_sub' f σ.length
  have hf0 : f 0 = 0 := by
    show workFnU C₀ (σ.take 0) ((WFAU hk C₀).conf (σ.take 0)) = 0
    rw [List.take_zero]
    have hc : (WFAU hk C₀).conf ([] : List M) = C₀ := rfl
    rw [hc]
    exact wfU_nil_self hk M C₀
  have hfn : offlineCost C₀ σ ≤ f σ.length := by
    have h := offlineCost_le_wfU k hk M C₀ σ (S σ.length)
    rw [hfdef]
    simpa using h
  rw [hsplit2, htel, hf0] at hcost
  linarith
