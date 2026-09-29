-- Prove2me | solution 1 for KServer.extended_cost_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:23:35.878766+00:00
-- url     : https://prove2.me/submissions/32567fce-91c1-40bb-bf4a-29dec7db58b1

import Mathlib
import Definitions.Def_KServer_workfunction
import Theorems.Thm_KServer_workFn_step_approx
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_offlineCost_le_workFn

open KServer

private theorem moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem moveCost_comm {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    moveCost A B = moveCost B A := by
  unfold moveCost; exact Finset.sum_congr rfl fun i _ => dist_comm _ _

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

/-- **The Extended Cost Lemma of Chrobak and Larmore.**  If the total growth of the work
function over a request sequence is at most `lam` times the offline optimum plus a constant,
then the Work Function Algorithm is `(lam - 1)`-competitive. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (lam c : ℝ)
    (H : ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M,
          workFn C₀ (σ.take (t + 1)) X ≤ workFn C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ lam * offlineCost C₀ σ + c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (lam - 1) := by
  classical
  -- an approximate minimiser for each (current configuration, past requests, new request)
  have hchoice : ∀ (Z : Config k M) (l : List M) (r : M),
      ∃ Y : Config k M, (∃ i, Y i = r) ∧
        workFn C₀ l Y + moveCost Y Z
          ≤ workFn C₀ (l ++ [r]) Z + (1:ℝ) / 2 ^ (l.length + 1) := by
    intro Z l r
    exact workFn_step_approx k hk M C₀ l r Z _ (by positivity)
  choose stp hstp1 hstp2 using hchoice
  -- the trajectory of the Work Function Algorithm
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
  set f : ℕ → ℝ := fun t => workFn C₀ (σ.take t) (Ct t) with hfdef
  have hlen : ∀ t : ℕ, t ≤ n → (σ.take t).length = t := by
    intro t ht; rw [List.length_take]; omega
  -- the per-step bound
  have hbound : ∀ t ∈ Finset.range n,
      moveCost (Ct t) (Ct (t + 1)) ≤ (f t - f (t + 1)) + u t + (1:ℝ) / 2 ^ (t + 1) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    have hts : σ.take (t + 1) = σ.take t ++ [σ[t]] := take_succ_eq σ t ht
    have hCs : Ct (t + 1) = stp (Ct t) (σ.take t) σ[t] := by
      rw [hCtdef]; simp only []; rw [hts, htraj_concat]
    have hcov : ∃ i, Ct (t + 1) i = σ[t] := by rw [hCs]; exact hstp1 _ _ _
    have hkey : workFn C₀ (σ.take t) (Ct (t + 1)) + moveCost (Ct (t + 1)) (Ct t)
        ≤ workFn C₀ (σ.take t ++ [σ[t]]) (Ct t) + (1:ℝ) / 2 ^ ((σ.take t).length + 1) := by
      rw [hCs]; exact hstp2 _ _ _
    rw [hlen t (by omega)] at hkey
    have hcovd : workFn C₀ (σ.take (t + 1)) (Ct (t + 1))
        = workFn C₀ (σ.take t) (Ct (t + 1)) := by
      rw [hts]; exact workFn_covered k hk M C₀ (σ.take t) σ[t] (Ct (t + 1)) hcov
    have hut := hu t ht (Ct t)
    have hcomm : moveCost (Ct t) (Ct (t + 1)) = moveCost (Ct (t + 1)) (Ct t) :=
      moveCost_comm _ _
    have hf1 : f t = workFn C₀ (σ.take t) (Ct t) := rfl
    have hf2 : f (t + 1) = workFn C₀ (σ.take (t + 1)) (Ct (t + 1)) := rfl
    rw [hcomm, hf1, hf2, hcovd]
    rw [← hts] at hkey
    linarith
  have hsum := Finset.sum_le_sum hbound
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_sub' f n] at hsum
  -- the endpoints of the telescoping sum
  have hf0 : f 0 = 0 := by
    have : Ct 0 = C₀ := by rw [hCtdef]; simp only []; rw [List.take_zero]; exact htraj_nil
    rw [hfdef]; simp only []; rw [List.take_zero, this, workFn_nil k hk M C₀ C₀, moveCost_self]
  have hfn : offlineCost C₀ σ ≤ f n := by
    have : f n = workFn C₀ σ (Ct n) := by
      rw [hfdef]; simp only []; rw [hn, List.take_length]
    rw [this]; exact offlineCost_le_workFn k hk M C₀ σ (Ct n)
  have hgeom := geom_half_le_one n
  -- the cost of the algorithm is that sum
  have hcost : (⟨traj, hserves⟩ : OnlineAlgorithm k M).cost σ
      = ∑ t ∈ Finset.range n, moveCost (Ct t) (Ct (t + 1)) := rfl
  rw [hcost]
  have : (⟨traj, hserves⟩ : OnlineAlgorithm k M).conf [] = C₀ := htraj_nil
  rw [this]
  linarith
