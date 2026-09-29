-- Prove2me | solution 1 for KServer.ckPotAtK_antipodal
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-07T17:16:52.612456+00:00
-- url     : https://prove2.me/submissions/ce12bbd2-afac-43ab-8802-42f06bae4bef

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k
import Theorems.Thm_KServer_workFnU_antipodal_extension_antipode

open KServer

/-- The number of antipodal servers of the `i`-th anchor configuration is `i + 1`. -/
private theorem lev_ckConfigK (k : ℕ) (M : Type) (x : Fin k → M) (i : Fin k) :
    ∑ j : Fin k, Sum.elim (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) (ckConfigK x i j)
      = ((i : ℕ) : ℝ) + 1 := by
  classical
  have hterm : ∀ j : Fin k,
      Sum.elim (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) (ckConfigK x i j)
        = if (j : ℕ) ≤ (i : ℕ) then (1:ℝ) else 0 := by
    intro j
    unfold ckConfigK
    by_cases h : (j : ℕ) ≤ (i : ℕ) <;> simp [h]
  have hik : (i : ℕ) < k := i.isLt
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Fin.sum_univ_eq_sum_range (fun j => if j ≤ (i : ℕ) then (1:ℝ) else 0) k]
  have hfil : (Finset.range k).filter (fun j => j ≤ (i : ℕ)) = Finset.range ((i : ℕ) + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, hfil]
  simp

/-- The projection of the `i`-th anchor configuration along the antipode map. -/
private theorem proj_ckConfigK (k : ℕ) (M : Type) (a : M → M) (x : Fin k → M) (i : Fin k) :
    (fun j => Sum.elim id a (ckConfigK x i j))
      = (fun j : Fin k => if (j : ℕ) ≤ (i : ℕ) then a (x i) else x j) := by
  funext j
  unfold ckConfigK
  by_cases h : (j : ℕ) ≤ (i : ℕ) <;> simp [h]

private theorem sum_index_succ (k : ℕ) :
    ∑ i : Fin k, (((i : ℕ) : ℝ) + 1) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring

/-- **The Coester--Koutsoupias potential of an antipodal space, computed intrinsically.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (a : M → M)
    (ha : ∀ x y : M, dist x (a y) = Δ - dist x y)
    (C₀ : Config k M) (σ : List M) (x : Fin k → M) :
    ckPotAtK k M Δ hΔ0 hΔ C₀ σ x
      = (workFnU C₀ σ x
          + ∑ i : Fin k, workFnU C₀ σ (fun j => if (j : ℕ) ≤ (i : ℕ) then a (x i) else x j))
        + Δ * ((k : ℝ) * ((k : ℝ) + 1) / 2) := by
  classical
  unfold ckPotAtK
  have hbase : @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun j => Sum.inl (x j))
        = workFnU C₀ σ x := by
    have h := workFnU_antipodal_extension_antipode k hk M Δ hΔ0 hΔ a ha C₀ σ
      (fun j => Sum.inl (x j))
    simpa using h
  have hanchor : ∀ i : Fin k, @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (ckConfigK x i)
        = workFnU C₀ σ (fun j => if (j : ℕ) ≤ (i : ℕ) then a (x i) else x j)
          + Δ * (((i : ℕ) : ℝ) + 1) := by
    intro i
    have h := workFnU_antipodal_extension_antipode k hk M Δ hΔ0 hΔ a ha C₀ σ (ckConfigK x i)
    rw [lev_ckConfigK k M x i, proj_ckConfigK k M a x i] at h
    exact h
  rw [hbase, Finset.sum_congr rfl (fun i _ => hanchor i), Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_index_succ k]
  ring
