-- Prove2me | solution 1 for KServer.extended_cost_lemma_unordered
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:41:45.168126+00:00
-- url     : https://prove2.me/submissions/c08f9495-77fe-4776-8fa7-c979e6d33e25

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_step_approx
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_offlineCost_le_workFn

open KServer

private theorem moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem moveCost_comm {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    moveCost A B = moveCost B A := by
  unfold moveCost; exact Finset.sum_congr rfl fun i _ => dist_comm _ _

/-- Any relabelling of the target bounds the unordered work function from above. -/
private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

/-- The minimum over relabellings is attained. -/
private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

/-- A relabelling may be moved from one argument of the movement cost to the other. -/
private theorem mc_reindex {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π⁻¹ : Equiv.Perm (Fin k))) Z = moveCost Y (Z ∘ π) := by
  unfold moveCost
  refine (Fintype.sum_equiv π (fun j => dist (Y j) ((Z ∘ π) j))
    (fun i => dist ((Y ∘ (π⁻¹ : Equiv.Perm (Fin k))) i) (Z i)) ?_).symm
  intro j
  simp

/-- Serving a request the configuration already covers leaves the unordered work function
unchanged. -/
private theorem wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine workFn_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

/-- The unordered form of the one-step recurrence, with the labelled movement cost. -/
private theorem wfU_step_approx (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Z : Config k M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : Config k M, (∃ i, Y i = r) ∧
      workFnU C₀ σ Y + moveCost Y Z ≤ workFnU C₀ (σ ++ [r]) Z + ε := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) Z
  obtain ⟨Y', hY'cov, hY'⟩ := workFn_step_approx k hk M C₀ σ r (Z ∘ π) ε hε
  refine ⟨Y' ∘ (π⁻¹ : Equiv.Perm (Fin k)), ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hY'cov
    exact ⟨π i, by simpa using hi⟩
  · have hcomp : (Y' ∘ (π⁻¹ : Equiv.Perm (Fin k))) ∘ (π : Equiv.Perm (Fin k)) = Y' := by
      funext i; simp
    have h1 : workFnU C₀ σ (Y' ∘ (π⁻¹ : Equiv.Perm (Fin k))) ≤ workFn C₀ σ Y' := by
      have := wfU_le C₀ σ (Y' ∘ (π⁻¹ : Equiv.Perm (Fin k))) π
      rwa [hcomp] at this
    have h2 := mc_reindex Y' Z π
    rw [← hπ]
    linarith

/-- The optimum is a lower bound for the unordered work function. -/
private theorem off_le_wfU (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    offlineCost C₀ σ ≤ workFnU C₀ σ X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
  rw [← hπ]
  exact offlineCost_le_workFn k hk M C₀ σ (X ∘ π)

/-- The unordered work function vanishes at the initial configuration before any request. -/
private theorem wfU_nil_self (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) : workFnU C₀ [] C₀ = 0 := by
  refine le_antisymm ?_ ?_
  · have h := wfU_le C₀ [] C₀ 1
    rw [show (C₀ ∘ (1 : Equiv.Perm (Fin k))) = C₀ from rfl,
      workFn_nil k hk M C₀ C₀, moveCost_self] at h
    exact h
  · obtain ⟨π, hπ⟩ := wfU_exists C₀ ([] : List M) C₀
    rw [← hπ, workFn_nil k hk M C₀ (C₀ ∘ π)]
    exact moveCost_nonneg _ _

/-- `σ.take (t+1)` is `σ.take t` with the `t`-th request appended. -/
private theorem take_succ_eq {M : Type} (σ : List M) (t : ℕ) (ht : t < σ.length) :
    σ.take (t + 1) = σ.take t ++ [σ[t]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  rfl

/-- The geometric slack accumulated by approximate minimisation is at most `1`. -/
private theorem geom_half_le_one (n : ℕ) :
    (∑ t ∈ Finset.range n, (1:ℝ) / 2 ^ (t + 1)) ≤ 1 := by
  have key : ∀ m : ℕ, (∑ t ∈ Finset.range m, (1:ℝ) / 2 ^ (t + 1)) = 1 - 1 / 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp
        ring
  rw [key]
  have h1 : (0:ℝ) < 2 ^ n := by positivity
  have h2 : (0:ℝ) ≤ 1 / 2 ^ n := by positivity
  linarith

/-- **The Extended Cost Lemma for the unordered work function.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (lam c : ℝ)
    (H : ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M,
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ lam * offlineCost C₀ σ + c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (lam - 1) := by
  classical
  have hchoice : ∀ (Z : Config k M) (l : List M) (r : M),
      ∃ Y : Config k M, (∃ i, Y i = r) ∧
        workFnU C₀ l Y + moveCost Y Z
          ≤ workFnU C₀ (l ++ [r]) Z + (1:ℝ) / 2 ^ (l.length + 1) := by
    intro Z l r
    exact wfU_step_approx k hk M C₀ l r Z _ (by positivity)
  choose stp hstp1 hstp2 using hchoice
  set traj : List M → Config k M := fun l =>
    List.reverseRecOn l C₀ (fun l r prev => stp prev l r) with htrajdef
  have htraj_nil : traj [] = C₀ := by simp [htrajdef]
  have htraj_concat : ∀ (l : List M) (r : M), traj (l ++ [r]) = stp (traj l) l r := by
    intro l r; simp [htrajdef]
  have hserves : ∀ (l : List M) (r : M), ∃ i, traj (l ++ [r]) i = r := by
    intro l r; rw [htraj_concat]; exact hstp1 _ _ _
  refine ⟨⟨traj, hserves⟩, htraj_nil, ⟨c + 1, fun σ => ?_⟩⟩
  obtain ⟨u, hu, husum⟩ := H σ
  set n := σ.length with hn
  set Ct : ℕ → Config k M := fun t => traj (σ.take t) with hCtdef
  set f : ℕ → ℝ := fun t => workFnU C₀ (σ.take t) (Ct t) with hfdef
  have hlen : ∀ t : ℕ, t ≤ n → (σ.take t).length = t := by
    intro t ht; rw [List.length_take]; omega
  have hbound : ∀ t ∈ Finset.range n,
      moveCost (Ct t) (Ct (t + 1)) ≤ (f t - f (t + 1)) + u t + (1:ℝ) / 2 ^ (t + 1) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    have hts : σ.take (t + 1) = σ.take t ++ [σ[t]] := take_succ_eq σ t ht
    have hCs : Ct (t + 1) = stp (Ct t) (σ.take t) σ[t] := by
      rw [hCtdef]; simp only []; rw [hts, htraj_concat]
    have hcov : ∃ i, Ct (t + 1) i = σ[t] := by rw [hCs]; exact hstp1 _ _ _
    have hkey : workFnU C₀ (σ.take t) (Ct (t + 1)) + moveCost (Ct (t + 1)) (Ct t)
        ≤ workFnU C₀ (σ.take t ++ [σ[t]]) (Ct t) + (1:ℝ) / 2 ^ ((σ.take t).length + 1) := by
      rw [hCs]; exact hstp2 _ _ _
    rw [hlen t (by omega)] at hkey
    have hcovd : workFnU C₀ (σ.take (t + 1)) (Ct (t + 1))
        = workFnU C₀ (σ.take t) (Ct (t + 1)) := by
      rw [hts]; exact wfU_covered k hk M C₀ (σ.take t) σ[t] (Ct (t + 1)) hcov
    have hut := hu t ht (Ct t)
    have hcomm : moveCost (Ct t) (Ct (t + 1)) = moveCost (Ct (t + 1)) (Ct t) :=
      moveCost_comm _ _
    have hf1 : f t = workFnU C₀ (σ.take t) (Ct t) := rfl
    have hf2 : f (t + 1) = workFnU C₀ (σ.take (t + 1)) (Ct (t + 1)) := rfl
    rw [hcomm, hf1, hf2, hcovd]
    rw [← hts] at hkey
    linarith
  have hsum := Finset.sum_le_sum hbound
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_sub' f n] at hsum
  have hf0 : f 0 = 0 := by
    have hc0 : Ct 0 = C₀ := by rw [hCtdef]; simp only []; rw [List.take_zero]; exact htraj_nil
    rw [hfdef]; simp only []; rw [List.take_zero, hc0, wfU_nil_self k hk M C₀]
  have hfn : offlineCost C₀ σ ≤ f n := by
    have he : f n = workFnU C₀ σ (Ct n) := by
      rw [hfdef]; simp only []; rw [hn, List.take_length]
    rw [he]; exact off_le_wfU k hk M C₀ σ (Ct n)
  have hgeom := geom_half_le_one n
  have hcost : (⟨traj, hserves⟩ : OnlineAlgorithm k M).cost σ
      = ∑ t ∈ Finset.range n, moveCost (Ct t) (Ct (t + 1)) := rfl
  rw [hcost]
  have hconf : (⟨traj, hserves⟩ : OnlineAlgorithm k M).conf [] = C₀ := htraj_nil
  rw [hconf]
  linarith
