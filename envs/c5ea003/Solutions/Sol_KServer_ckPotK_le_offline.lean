-- Prove2me | solution 1 for KServer.ckPotK_le_offline
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-07T10:50:44.076716+00:00
-- url     : https://prove2.me/submissions/cb235fb8-ca2a-438b-bd34-344b995ecae4

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k
import Theorems.Thm_KServer_workFnU_antipodal_extension_restrict
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFn_workFnU_sandwich

open KServer

namespace CKOff

theorem moveCost_nonneg {k : ℕ} {N : Type} [MetricSpace N] (C D : Config k N) :
    0 ≤ moveCost C D :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

/-- The set of costs whose infimum defines the work function is bounded below by `0`. -/
theorem bddBelow_workFn_set {k : ℕ} {N : Type} [MetricSpace N] (C₀ : Config k N) (σ : List N)
    (X : Config k N) :
    BddBelow {c : ℝ | ∃ S : ℕ → Config k N, ServesFrom C₀ σ S ∧
      c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X} := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h₁ : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun _ _ => moveCost_nonneg _ _
  have h₂ : (0:ℝ) ≤ moveCost (S σ.length) X := moveCost_nonneg _ _
  linarith

/-- The set of costs whose infimum defines the offline optimum is bounded below by `0`. -/
theorem bddBelow_offline_set {k : ℕ} {N : Type} [MetricSpace N] (C₀ : Config k N) (σ : List N) :
    BddBelow {c : ℝ | ∃ S : ℕ → Config k N, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  exact Finset.sum_nonneg fun _ _ => moveCost_nonneg _ _

/-- Any schedule serving `σ` bounds the work function at its own final configuration. -/
theorem workFn_le_of_serves {k : ℕ} {N : Type} [MetricSpace N] (C₀ : Config k N) (σ : List N)
    (S : ℕ → Config k N) (hS : ServesFrom C₀ σ S) :
    workFn C₀ σ (S σ.length) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      ∈ {c : ℝ | ∃ T : ℕ → Config k N, ServesFrom C₀ σ T ∧
        c = (∑ j ∈ Finset.range σ.length, moveCost (T j) (T (j + 1)))
          + moveCost (T σ.length) (S σ.length)} := by
    refine ⟨S, hS, ?_⟩
    have : moveCost (S σ.length) (S σ.length) = 0 := by
      unfold moveCost; simp
    rw [this, add_zero]
  exact csInf_le (bddBelow_workFn_set C₀ σ (S σ.length)) hmem

/-- The offline cost set is nonempty: coalescing all servers on the current request serves `σ`. -/
theorem offline_set_nonempty {k : ℕ} {N : Type} [MetricSpace N] (hk : 1 ≤ k) (C₀ : Config k N)
    (σ : List N) :
    ({c : ℝ | ∃ S : ℕ → Config k N, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))}).Nonempty := by
  classical
  have hk0 : 0 < k := hk
  set c₀ : N := C₀ ⟨0, hk0⟩ with hc₀
  set S : ℕ → Config k N := fun n => if n = 0 then C₀ else fun _ => σ.getD (n - 1) c₀ with hS
  refine ⟨_, S, ⟨by simp [hS], ?_⟩, rfl⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  have hj : (j : ℕ) < σ.length := j.isLt
  simp only [hS, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem _ _ hj, List.get_eq_getElem]

theorem card_le_filter (k : ℕ) (i : Fin k) :
    (Finset.univ.filter (fun j : Fin k => (j : ℕ) ≤ (i : ℕ))).card = (i : ℕ) + 1 := by
  have h : (Finset.univ.filter (fun j : Fin k => (j : ℕ) ≤ (i : ℕ))) = Finset.Iic i :=
    Finset.ext fun j => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_def]
  rw [h, Fin.card_Iic]

theorem gauss_sum (k : ℕ) (Δ : ℝ) :
    ∑ i : Fin k, (2 * Δ * (((i : ℕ) : ℝ) + 1)) = Δ * k * (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    push_cast
    ring

/-- Moving from the anchors to the `i`-th anchor configuration costs at most `2Δ(i+1)`. -/
theorem move_to_anchor_le {k : ℕ} {M : Type} [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (x : Fin k → M) (i : Fin k) :
    @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun j => Sum.inl (x j)) (ckConfigK x i)
      ≤ 2 * Δ * (((i : ℕ) : ℝ) + 1) := by
  have hterm : @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun j => Sum.inl (x j)) (ckConfigK x i)
      = ∑ j : Fin k, (if (j : ℕ) ≤ (i : ℕ) then 2 * Δ - dist (x j) (x i) else 0) := by
    unfold moveCost
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (j : ℕ) ≤ (i : ℕ) <;> simp [ckConfigK, h, antipodalExtension_dist]
  rw [hterm]
  have hle : ∑ j : Fin k, (if (j : ℕ) ≤ (i : ℕ) then 2 * Δ - dist (x j) (x i) else 0)
      ≤ ∑ j : Fin k, (if (j : ℕ) ≤ (i : ℕ) then 2 * Δ else 0) := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases h : (j : ℕ) ≤ (i : ℕ)
    · simp only [h, if_true]
      have := dist_nonneg (x := x j) (y := x i)
      linarith
    · simp [h]
  refine hle.trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_le_filter, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

end CKOff

open CKOff in
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) :
    ckPotK k M Δ hΔ0 hΔ C₀ σ
      ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + Δ * (k : ℝ) * ((k : ℝ) + 1) := by
  classical
  -- the anchored potential at `x` is at most `(k+1) * workFnU C₀ σ x + Δ k (k+1)`
  have hanchor : ∀ x : Fin k → M,
      ckPotK k M Δ hΔ0 hΔ C₀ σ
        ≤ ((k : ℝ) + 1) * workFnU C₀ σ x + Δ * (k : ℝ) * ((k : ℝ) + 1) := by
    intro x
    have hbase : @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun j => Sum.inl (x j))
        = workFnU C₀ σ x :=
      workFnU_antipodal_extension_restrict k hk M Δ hΔ0 hΔ C₀ σ x
    have hterm : ∀ i : Fin k, @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (ckConfigK x i)
        ≤ workFnU C₀ σ x + 2 * Δ * (((i : ℕ) : ℝ) + 1) := by
      intro i
      have h1 := @workFnU_lipschitz k hk (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (ckConfigK x i) (fun j => Sum.inl (x j))
      have h2 := move_to_anchor_le (M := M) Δ hΔ0 hΔ x i
      rw [hbase] at h1
      linarith
    have hsum : ∑ i : Fin k, @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (ckConfigK x i)
        ≤ ∑ i : Fin k, (workFnU C₀ σ x + 2 * Δ * (((i : ℕ) : ℝ) + 1)) :=
      Finset.sum_le_sum fun i _ => hterm i
    have hgauss : ∑ i : Fin k, (workFnU C₀ σ x + 2 * Δ * (((i : ℕ) : ℝ) + 1))
        = (k : ℝ) * workFnU C₀ σ x + Δ * (k : ℝ) * ((k : ℝ) + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, gauss_sum]
      simp [nsmul_eq_mul]
    have hpot := ckPotK_le k M Δ hΔ0 hΔ C₀ σ x
    unfold ckPotAtK at hpot
    rw [hbase] at hpot
    rw [hgauss] at hsum
    linarith
  -- compare with the offline optimum
  set D : ℝ := Δ * (k : ℝ) * ((k : ℝ) + 1) with hD
  have hkpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hkey : (ckPotK k M Δ hΔ0 hΔ C₀ σ - D) / ((k : ℝ) + 1) ≤ offlineCost C₀ σ := by
    refine le_csInf (offline_set_nonempty hk C₀ σ) ?_
    rintro c ⟨S, hS, rfl⟩
    have h1 : workFn C₀ σ (S σ.length)
        ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
      workFn_le_of_serves C₀ σ S hS
    have h2 : workFnU C₀ σ (S σ.length) ≤ workFn C₀ σ (S σ.length) :=
      (workFn_workFnU_sandwich k hk M C₀ σ (S σ.length) Δ hΔ).1
    have h3 := hanchor (S σ.length)
    rw [div_le_iff₀ hkpos]
    nlinarith
  rw [div_le_iff₀ hkpos] at hkey
  linarith
