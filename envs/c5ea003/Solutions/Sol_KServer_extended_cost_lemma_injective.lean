-- Prove2me | solution 1 for KServer.extended_cost_lemma_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:21:47.334681+00:00
-- url     : https://prove2.me/submissions/9064158d-dc71-4a96-81e7-b9dbb263bad9

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_step_approx
import Theorems.Thm_KServer_moveCost_injective_between
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_workFn_lipschitz
import Theorems.Thm_KServer_offlineCost_le_workFn

open KServer

private theorem moveCost_self {k : ℕ} {M : Type} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem moveCost_comm {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    moveCost A B = moveCost B A := by
  unfold moveCost; exact Finset.sum_congr rfl fun i _ => dist_comm _ _

private theorem moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k)))
      = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem wfU_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ σ Y + moveCost Y X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ Y
  have h1 := wfU_le C₀ σ X π
  have h2 := workFn_lipschitz k hk M C₀ σ (X ∘ π) (Y ∘ π)
  have h3 := mc_perm Y X π
  rw [hπ] at h2
  linarith

private theorem wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine workFn_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

private theorem off_le_wfU (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    offlineCost C₀ σ ≤ workFnU C₀ σ X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
  rw [← hπ]
  exact offlineCost_le_workFn k hk M C₀ σ (X ∘ π)

private theorem wfU_nil_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ X₀ : Config k M) : workFnU C₀ [] X₀ ≤ moveCost C₀ X₀ := by
  have h := wfU_le C₀ [] X₀ 1
  rw [show (X₀ ∘ (1 : Equiv.Perm (Fin k))) = X₀ from rfl, workFn_nil k hk M C₀ X₀] at h
  exact h

private theorem take_succ_eq {M : Type} (σ : List M) (t : ℕ) (ht : t < σ.length) :
    σ.take (t + 1) = σ.take t ++ [σ[t]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  rfl

private theorem geom_half_le_one (n : ℕ) :
    (∑ t ∈ Finset.range n, (1:ℝ) / 2 ^ (t + 1)) ≤ 1 := by
  have key : ∀ m : ℕ, (∑ t ∈ Finset.range m, (1:ℝ) / 2 ^ (t + 1)) = 1 - 1 / 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; field_simp; ring
  rw [key]
  have h1 : (0:ℝ) < 2 ^ n := by positivity
  have h2 : (0:ℝ) ≤ 1 / 2 ^ n := by positivity
  linarith

/-- **The Extended Cost Lemma, with the growth bound required only at injective
configurations.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ X₀ : Config k M) (hX₀ : Function.Injective X₀) (lam c : ℝ)
    (H : ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ lam * offlineCost C₀ σ + c) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (lam - 1) := by
  classical
  -- an injective approximate minimiser at every injective current configuration
  have hchoice : ∀ (Z : Config k M) (l : List M) (r : M),
      ∃ Y : Config k M, Function.Injective Z →
        (Function.Injective Y ∧ (∃ i, Y i = r) ∧
          workFnU C₀ l Y + moveCost Y Z
            ≤ workFnU C₀ (l ++ [r]) Z + (1:ℝ) / 2 ^ (l.length + 1)) := by
    intro Z l r
    by_cases hZ : Function.Injective Z
    · obtain ⟨Y0, hY0cov, hY0⟩ :=
        workFnU_step_approx k hk M C₀ l r Z ((1:ℝ) / 2 ^ (l.length + 1)) (by positivity)
      obtain ⟨Y1, hinj, hcov, hbet⟩ := moveCost_injective_between k M Y0 Z hZ r hY0cov
      refine ⟨Y1, fun _ => ⟨hinj, hcov, ?_⟩⟩
      have hlip := wfU_lipschitz k hk M C₀ l Y1 Y0
      linarith
    · exact ⟨Z, fun h => absurd h hZ⟩
  choose stp hstp using hchoice
  set traj : List M → Config k M := fun l =>
    List.reverseRecOn l X₀ (fun l r prev => stp prev l r) with htrajdef
  have htraj_nil : traj [] = X₀ := by simp [htrajdef]
  have htraj_concat : ∀ (l : List M) (r : M), traj (l ++ [r]) = stp (traj l) l r := by
    intro l r; simp [htrajdef]
  have htraj_inj : ∀ l : List M, Function.Injective (traj l) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => rw [htraj_nil]; exact hX₀
    | append_singleton l r ih => rw [htraj_concat]; exact (hstp (traj l) l r ih).1
  set conf : List M → Config k M := fun l => if l = [] then C₀ else traj l with hconfdef
  have hconf_nil : conf [] = C₀ := by simp [hconfdef]
  have hconf_ne : ∀ l : List M, l ≠ [] → conf l = traj l := by
    intro l hl; simp [hconfdef, hl]
  have hserves : ∀ (l : List M) (r : M), ∃ i, conf (l ++ [r]) i = r := by
    intro l r
    rw [hconf_ne _ (by simp), htraj_concat]
    exact (hstp (traj l) l r (htraj_inj l)).2.1
  refine ⟨⟨conf, hserves⟩, hconf_nil, ⟨c + 1 + 2 * moveCost C₀ X₀, fun σ => ?_⟩⟩
  obtain ⟨u, hu, husum⟩ := H σ
  set n := σ.length with hn
  set D : ℕ → Config k M := fun t => traj (σ.take t) with hDdef
  set f : ℕ → ℝ := fun t => workFnU C₀ (σ.take t) (D t) with hfdef
  have hlen : ∀ t : ℕ, t ≤ n → (σ.take t).length = t := by
    intro t ht; rw [List.length_take]; omega
  -- the per-step bound along the trajectory
  have hbound : ∀ t ∈ Finset.range n,
      moveCost (D t) (D (t + 1)) ≤ (f t - f (t + 1)) + u t + (1:ℝ) / 2 ^ (t + 1) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    have hts : σ.take (t + 1) = σ.take t ++ [σ[t]] := take_succ_eq σ t ht
    have hDs : D (t + 1) = stp (D t) (σ.take t) σ[t] := by
      rw [hDdef]; simp only []; rw [hts, htraj_concat]
    have hspec := hstp (D t) (σ.take t) σ[t] (htraj_inj (σ.take t))
    have hcov : ∃ i, D (t + 1) i = σ[t] := by rw [hDs]; exact hspec.2.1
    have hkey : workFnU C₀ (σ.take t) (D (t + 1)) + moveCost (D (t + 1)) (D t)
        ≤ workFnU C₀ (σ.take t ++ [σ[t]]) (D t) + (1:ℝ) / 2 ^ ((σ.take t).length + 1) := by
      rw [hDs]; exact hspec.2.2
    rw [hlen t (by omega)] at hkey
    have hcovd : workFnU C₀ (σ.take (t + 1)) (D (t + 1))
        = workFnU C₀ (σ.take t) (D (t + 1)) := by
      rw [hts]; exact wfU_covered k hk M C₀ (σ.take t) σ[t] (D (t + 1)) hcov
    have hut := hu t ht (D t) (htraj_inj (σ.take t))
    have hcomm : moveCost (D t) (D (t + 1)) = moveCost (D (t + 1)) (D t) := moveCost_comm _ _
    have hf1 : f t = workFnU C₀ (σ.take t) (D t) := rfl
    have hf2 : f (t + 1) = workFnU C₀ (σ.take (t + 1)) (D (t + 1)) := rfl
    rw [hcomm, hf1, hf2, hcovd]
    rw [← hts] at hkey
    linarith
  have hsum := Finset.sum_le_sum hbound
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_sub' f n] at hsum
  have hf0 : f 0 ≤ moveCost C₀ X₀ := by
    have hD0 : D 0 = X₀ := by rw [hDdef]; simp only []; rw [List.take_zero]; exact htraj_nil
    rw [hfdef]; simp only []; rw [List.take_zero, hD0]
    exact wfU_nil_le k hk M C₀ X₀
  have hfn : offlineCost C₀ σ ≤ f n := by
    have he : f n = workFnU C₀ σ (D n) := by rw [hfdef]; simp only []; rw [hn, List.take_length]
    rw [he]; exact off_le_wfU k hk M C₀ σ (D n)
  have hgeom := geom_half_le_one n
  -- the algorithm's cost differs from the trajectory's only at the first step
  have hcostle : (⟨conf, hserves⟩ : OnlineAlgorithm k M).cost σ
      ≤ (∑ t ∈ Finset.range n, moveCost (D t) (D (t + 1))) + moveCost C₀ X₀ := by
    have hterm : ∀ t ∈ Finset.range n,
        moveCost (conf (σ.take t)) (conf (σ.take (t + 1)))
          ≤ moveCost (D t) (D (t + 1)) + (if t = 0 then moveCost C₀ X₀ else 0) := by
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
        have hD0 : D 0 = X₀ := by rw [hDdef]; simp only []; rw [List.take_zero]; exact htraj_nil
        rw [List.take_zero, hconf_nil, if_pos rfl]
        have := moveCost_triangle C₀ X₀ (traj (σ.take 1))
        have hD1 : D 1 = traj (σ.take 1) := rfl
        rw [hD0, hD1]
        linarith
      · have hne0 : σ.take t ≠ [] := by
          intro h
          have := congrArg List.length h
          rw [hlen t (by omega)] at this
          exact ht0 this
        rw [hconf_ne _ hne0, if_neg ht0]
        have h1 : D t = traj (σ.take t) := rfl
        have h2 : D (t + 1) = traj (σ.take (t + 1)) := rfl
        rw [← h1, ← h2]
        linarith
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range n) 0
      (fun _ => moveCost C₀ X₀)] at this
    have hmc : (0:ℝ) ≤ moveCost C₀ X₀ := moveCost_nonneg _ _
    have hsplit : (if (0:ℕ) ∈ Finset.range n then moveCost C₀ X₀ else 0) ≤ moveCost C₀ X₀ := by
      split <;> linarith
    calc (⟨conf, hserves⟩ : OnlineAlgorithm k M).cost σ
        = ∑ t ∈ Finset.range n, moveCost (conf (σ.take t)) (conf (σ.take (t + 1))) := rfl
      _ ≤ _ := this
      _ ≤ (∑ t ∈ Finset.range n, moveCost (D t) (D (t + 1))) + moveCost C₀ X₀ := by linarith
  have hconf0 : (⟨conf, hserves⟩ : OnlineAlgorithm k M).conf [] = C₀ := hconf_nil
  rw [hconf0]
  linarith
