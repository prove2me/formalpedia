-- Prove2me | solution 1 for KServer.resolve_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T19:52:18.339747+00:00
-- url     : https://prove2.me/submissions/e23ef8b8-5593-4d7e-9ed0-64a9874a0390

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_mono
import Theorems.Thm_KServer_workFn_approx_offlineCost
import Theorems.Thm_KServer_workFnU_quasiconvex_three
import Theorems.Thm_KServer_workFnU_lipschitz
import Definitions.Def_KServer_lazy_potential

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem wfU_self {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  simpa using wfU_le C₀ σ X 1

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k))) = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem sum_perm {k : ℕ} {M : Type} [MetricSpace M] (v : M) (Y : Config k M)
    (π : Equiv.Perm (Fin k)) : ∑ i, dist v (Y (π i)) = ∑ i, dist v (Y i) :=
  Fintype.sum_equiv π (fun i => dist v (Y (π i))) (fun i => dist v (Y i)) (fun i => rfl)

/-- The distance between the endpoints of a walk is at most its length. -/
private theorem dist_telescope {M : Type} [MetricSpace M] (f : ℕ → M) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ j ∈ Finset.range n, dist (f j) (f (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := dist_triangle (f 0) (f n) (f (n + 1))
      linarith

/-- The work function grows at unit rate away from the initial configuration: measured from
any base point, the target's total distance is paid for. -/
private theorem wfU_lower (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (v : M) (X : Config k M) :
    (∑ i, dist v (X i)) - (∑ i, dist v (C₀ i)) ≤ workFnU C₀ σ X := by
  classical
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
  rw [← hπ, ← sum_perm v X π]
  set Y : Config k M := X ∘ (π : Equiv.Perm (Fin k)) with hY
  show (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i)) ≤ workFn C₀ σ Y
  have hbdd : BddBelow {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) Y} := by
    refine ⟨0, ?_⟩
    rintro c ⟨S, -, rfl⟩
    have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => dist_nonneg
    have h2 : (0:ℝ) ≤ moveCost (S σ.length) Y := Finset.sum_nonneg fun i _ => dist_nonneg
    linarith
  have hne : {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) Y}.Nonempty := by
    have hk0 : (0 : ℕ) < k := hk
    refine ⟨_, ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩),
      ⟨by simp, ?_⟩, rfl⟩⟩
    intro j
    refine ⟨⟨0, hk0⟩, ?_⟩
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem σ _ j.2]
    simp
  refine le_csInf hne ?_
  rintro c ⟨S, hS, rfl⟩
  have hcost : ∑ i, dist (C₀ i) (S σ.length i)
      ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
    have hswap : ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))
        = ∑ i, ∑ j ∈ Finset.range σ.length, dist (S j i) (S (j + 1) i) := by
      unfold moveCost
      exact Finset.sum_comm
    rw [hswap]
    refine Finset.sum_le_sum fun i _ => ?_
    have := dist_telescope (fun j => S j i) σ.length
    rw [hS.1] at this
    exact this
  have hfin : ∑ i, dist (C₀ i) (Y i)
      ≤ (∑ i, dist (C₀ i) (S σ.length i)) + moveCost (S σ.length) Y := by
    unfold moveCost
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _
  have hbase : (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i)) ≤ ∑ i, dist (C₀ i) (Y i) := by
    have : ∀ i : Fin k, dist v (Y i) - dist v (C₀ i) ≤ dist (C₀ i) (Y i) := by
      intro i
      have := dist_triangle v (C₀ i) (Y i)
      linarith
    calc (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i))
        = ∑ i, (dist v (Y i) - dist v (C₀ i)) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, dist (C₀ i) (Y i) := Finset.sum_le_sum fun i _ => this i
  linarith

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

private theorem wfU_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  rw [← hπ]
  exact le_trans (wfU_le C₀ σ X π) (workFn_mono k hk M C₀ σ r (X ∘ π))

/-- One step of the recurrence, expressed purely in the new work function. -/
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

section Perm
variable {M : Type} [MetricSpace M]

private theorem perm3_eq (C₀ : Config 3 M) (σ : List M) (X Y : Config 3 M)
    (τ : Equiv.Perm (Fin 3)) (h : ∀ i, X i = Y (τ i)) :
    workFnU C₀ σ X = workFnU C₀ σ Y := by
  rw [show X = Y ∘ (τ : Equiv.Perm (Fin 3)) from funext h]
  exact workFnU_perm 3 M C₀ σ Y τ

private theorem swap01 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![q, p, z] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 0 1) ?_
  intro i
  match i with
  | 0 => show p = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 0); rw [Equiv.swap_apply_left]; rfl
  | 1 => show q = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 1); rw [Equiv.swap_apply_right]; rfl
  | 2 => show z = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 2)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl

private theorem rot3 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![z, p, q] := by
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have c0 : c 0 = 1 := by rw [hc]; decide
  have c1 : c 1 = 2 := by rw [hc]; decide
  have c2 : c 2 = 0 := by rw [hc]; decide
  refine perm3_eq C₀ σ _ _ c ?_
  intro i
  match i with
  | 0 => show p = ![z, p, q] (c 0); rw [c0]; rfl
  | 1 => show q = ![z, p, q] (c 1); rw [c1]; rfl
  | 2 => show z = ![z, p, q] (c 2); rw [c2]; rfl

private theorem swap12 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![p, z, q] :=
  ((rot3 C₀ σ p z q).trans (swap01 C₀ σ q p z)).symm

/-- The Lipschitz property in pinned two-point form. -/
private theorem lipP (C₀ : Config 3 M) (σ : List M) (r u v v' : M) :
    workFnU C₀ σ ![r, u, v'] ≤ workFnU C₀ σ ![r, v, v'] + dist v u := by
  have hmc : moveCost (![r, v, v'] : Config 3 M) (![r, u, v'] : Config 3 M) = dist v u := by
    unfold moveCost
    rw [Fin.sum_univ_three]
    show dist r r + dist v u + dist v' v' = dist v u
    rw [dist_self, dist_self]; ring
  have h := workFnU_lipschitz 3 (by norm_num) M C₀ σ ![r, u, v'] ![r, v, v']
  rw [hmc] at h
  exact h

end Perm

section Resolve
variable {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M)

private theorem upd3_0 (X : Config 3 M) (u : M) :
    Function.update X 0 u = ![u, X 1, X 2] := by
  funext i
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp

private theorem upd3_1 (X : Config 3 M) (u : M) :
    Function.update X 1 u = ![X 0, u, X 2] := by
  funext i
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp

private theorem upd3_2 (X : Config 3 M) (u : M) :
    Function.update X 2 u = ![X 0, X 1, u] := by
  funext i
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp

private theorem lip3 (a b c a' b' c' : M) :
    workFnU C₀ σ ![a, b, c] ≤ workFnU C₀ σ ![a', b', c']
      + (dist a' a + dist b' b + dist c' c) := by
  have hmc : moveCost (![a', b', c'] : Config 3 M) (![a, b, c] : Config 3 M)
      = dist a' a + dist b' b + dist c' c := by
    unfold moveCost
    rw [Fin.sum_univ_three]
    rfl
  have h := workFnU_lipschitz 3 (by norm_num) M C₀ σ ![a, b, c] ![a', b', c']
  rw [hmc] at h
  exact h

end Resolve

/-- **Monotonicity of resolutions.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r x y z : M)
    (hres : workFnU C₀ (σ ++ [r]) ![x, y, z] = workFnU C₀ (σ ++ [r]) ![r, y, z] + dist r x) :
    workFnU C₀ (σ ++ [r]) ![x, x, z] = workFnU C₀ (σ ++ [r]) ![r, x, z] + dist r x := by
  obtain ⟨i, hi⟩ := wfU_step_self 3 (by norm_num) M C₀ σ r ![x, x, z]
  have e0 : (![x, x, z] : Config 3 M) 0 = x := rfl
  have e1 : (![x, x, z] : Config 3 M) 1 = x := rfl
  have e2 : (![x, x, z] : Config 3 M) 2 = z := rfl
  match i with
  | 0 =>
      rw [upd3_0, e0, e1, e2] at hi
      exact hi
  | 1 =>
      rw [upd3_1, e0, e1, e2, swap01 C₀ (σ ++ [r]) x r z] at hi
      exact hi
  | 2 =>
      rw [upd3_2, e0, e1, e2] at hi
      -- the exceptional case: `![x,x,z]` resolves at `z`
      have hq := workFnU_quasiconvex_three M C₀ (σ ++ [r]) r y z x x
      rw [min_self] at hq
      have l1 : workFnU C₀ (σ ++ [r]) ![x, y, z]
          ≤ workFnU C₀ (σ ++ [r]) ![x, y, r] + dist r z := by
        have := lip3 C₀ (σ ++ [r]) x y z x y r
        simp only [dist_self] at this
        linarith
      have l2 : workFnU C₀ (σ ++ [r]) ![x, x, z]
          ≤ workFnU C₀ (σ ++ [r]) ![x, r, z] + dist r x := by
        have := lip3 C₀ (σ ++ [r]) x x z x r z
        simp only [dist_self] at this
        linarith
      have s1 : workFnU C₀ (σ ++ [r]) ![x, r, z] = workFnU C₀ (σ ++ [r]) ![r, x, z] :=
        swap01 C₀ (σ ++ [r]) x r z
      have s2 : workFnU C₀ (σ ++ [r]) ![x, y, r] = workFnU C₀ (σ ++ [r]) ![r, x, y] :=
        rot3 C₀ (σ ++ [r]) x y r
      have s3 : workFnU C₀ (σ ++ [r]) ![r, y, x] = workFnU C₀ (σ ++ [r]) ![r, x, y] :=
        swap12 C₀ (σ ++ [r]) r y x
      have s4 : workFnU C₀ (σ ++ [r]) ![r, z, x] = workFnU C₀ (σ ++ [r]) ![r, x, z] :=
        swap12 C₀ (σ ++ [r]) r z x
      have s5 : workFnU C₀ (σ ++ [r]) ![x, x, r] = workFnU C₀ (σ ++ [r]) ![r, x, x] := by
        rw [rot3 C₀ (σ ++ [r]) x x r]
      rw [s1] at l2
      rw [s2] at l1
      rw [s5] at hi
      linarith
