-- Prove2me | solution 2 for CayleyCensus.walkCount_two_mul_le_walkCount_two_mul_one
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:49.777662+00:00
-- url     : https://prove2.me/submissions/a9bfee13-47db-4f33-b2bb-b877f6a978c2

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace CayleyCensus

private theorem two_mul_mul_le_sq_add_sq_aux (a b : ℕ) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  have hz : (0 : ℤ) ≤ ((a : ℤ) - (b : ℤ)) ^ 2 := sq_nonneg _
  have hint : (2 * (a * b) : ℤ) ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by nlinarith
  exact_mod_cast hint

private theorem sum_inv_aux {S : Finset G} (hS : InvClosed S) (f : G → ℕ) :
    ∑ s ∈ S, f s⁻¹ = ∑ s ∈ S, f s :=
  Finset.sum_nbij' (i := fun s => s⁻¹) (j := fun s => s⁻¹)
    (fun _ ha => hS ha) (fun _ ha => hS ha)
    (fun a _ => inv_inv a) (fun a _ => inv_inv a) (fun _ _ => rfl)

private theorem walkCount_inv_aux {S : Finset G} (hS : InvClosed S) (n : ℕ) (g : G) :
    walkCount S n g⁻¹ = walkCount S n g := by
  induction n generalizing g with
  | zero => simp [inv_eq_one]
  | succ n ih =>
      rw [walkCount_succ, walkCount_succ_right]
      have hcongr : ∀ s ∈ S, walkCount S n (s⁻¹ * g⁻¹) = walkCount S n (g * s) := by
        intro s _
        have hrw : s⁻¹ * g⁻¹ = (g * s)⁻¹ := by rw [mul_inv_rev]
        rw [hrw, ih]
      rw [Finset.sum_congr rfl hcongr]
      exact (sum_inv_aux hS (fun s => walkCount S n (g * s))).symm

private theorem walkCount_add_aux (S : Finset G) (m n : ℕ) (g : G) :
    walkCount S (m + n) g = ∑ h : G, walkCount S m h * walkCount S n (h⁻¹ * g) := by
  induction m generalizing g with
  | zero =>
      simp only [Nat.zero_add, walkCount_zero, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
      simp
  | succ m ih =>
      have hsucc : m + 1 + n = (m + n) + 1 := by omega
      rw [hsucc, walkCount_succ]
      have hstep : ∀ s : G, walkCount S (m + n) (s⁻¹ * g)
          = ∑ h : G, walkCount S m h * walkCount S n (h⁻¹ * (s⁻¹ * g)) :=
        fun s => ih _
      rw [Finset.sum_congr rfl (fun s _ => hstep s)]
      have hRHS : ∑ h : G, walkCount S (m + 1) h * walkCount S n (h⁻¹ * g)
          = ∑ s ∈ S, ∑ h : G, walkCount S m (s⁻¹ * h) * walkCount S n (h⁻¹ * g) := by
        simp only [walkCount_succ, Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [hRHS]
      refine Finset.sum_congr rfl fun s _ => ?_
      refine (Fintype.sum_equiv (Equiv.mulLeft s⁻¹) _ _ fun h => ?_).symm
      have h2 : (s⁻¹ * h)⁻¹ * (s⁻¹ * g) = h⁻¹ * g := by group
      simp only [Equiv.coe_mulLeft]
      rw [h2]

private theorem walkCount_two_mul_one_eq_sum_sq_aux {S : Finset G} (hS : InvClosed S)
    (n : ℕ) : walkCount S (2 * n) (1 : G) = ∑ h : G, walkCount S n h ^ 2 := by
  have h2 : 2 * n = n + n := by ring
  rw [h2, walkCount_add_aux]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_one, walkCount_inv_aux hS, sq]

theorem solution {S : Finset G} (hS : InvClosed S) (n : ℕ) (g : G) :
    walkCount S (2 * n) g ≤ walkCount S (2 * n) (1 : G) := by
  set a : G → ℕ := fun h => walkCount S n h with ha
  set b : G → ℕ := fun h => walkCount S n (g⁻¹ * h) with hb
  have hsplit : 2 * n = n + n := by ring
  have hg : walkCount S (2 * n) g = ∑ h : G, a h * b h := by
    rw [hsplit, walkCount_add_aux]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hinv : h⁻¹ * g = (g⁻¹ * h)⁻¹ := by group
    rw [ha, hb, hinv, walkCount_inv_aux hS]
  have h1 : walkCount S (2 * n) (1 : G) = ∑ h : G, a h ^ 2 :=
    walkCount_two_mul_one_eq_sum_sq_aux hS n
  have hshift : ∑ h : G, b h ^ 2 = ∑ h : G, a h ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => by simp [ha, hb]
  have hCS : 2 * ∑ h : G, a h * b h ≤ 2 * ∑ h : G, a h ^ 2 := by
    have hterm : ∀ h : G, 2 * (a h * b h) ≤ a h ^ 2 + b h ^ 2 :=
      fun h => two_mul_mul_le_sq_add_sq_aux (a h) (b h)
    calc 2 * ∑ h : G, a h * b h = ∑ h : G, 2 * (a h * b h) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ h : G, (a h ^ 2 + b h ^ 2) := Finset.sum_le_sum fun h _ => hterm h
      _ = (∑ h : G, a h ^ 2) + ∑ h : G, b h ^ 2 := by rw [Finset.sum_add_distrib]
      _ = 2 * ∑ h : G, a h ^ 2 := by rw [hshift]; ring
  rw [hg, h1]
  omega

end CayleyCensus

open CayleyCensus

theorem solution {S : Finset G} (hS : InvClosed S) (n : ℕ) (g : G) :
    walkCount S (2 * n) g ≤ walkCount S (2 * n) (1 : G) :=
  CayleyCensus.solution hS n g

#print axioms solution
