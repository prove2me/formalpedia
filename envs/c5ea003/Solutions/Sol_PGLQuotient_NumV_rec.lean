-- Prove2me | solution 1 for PGLQuotient.NumV_rec
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:06:09.319182+00:00
-- url     : https://prove2.me/submissions/feaffcf8-db58-43e2-8790-3ca211a67c71

import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Algebra/PGLQuotient/VolumeAlgebra.lean ====
/-!
# The algebraic core of the general-rank vertex volume

This file contains the purely algebraic input for the closed product form of the vertex volume
of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in **arbitrary rank**.

The building-theoretic side (see `Algebra.PGLQuotient.TwistedWeight` and
`Algebra.PGLQuotient.VertexVolumeGeneral`) produces a two-parameter family of *twisted masses*
`M(n,c,j)` (rank `n+1`, twist parameters `c` and `j`) satisfying a row-peeling recursion.  The
solution of that recursion is

`M(n,c,j) = NumV q n c j / DenV q n c j`,

where

* `NumV q n c j = ∑_{i=0}^{n} q^{ci} (∏_{k<i} (q^{n-k}-1)) (∏_{s<n-i}(q^{s+1+j}-1))`,
* `DenV q n c j = (∏_{s<n+1}(q^{s+1+j}-1)) (∏_{k<n}(q^{k+1}-1)) (∏_{k<n}(q^{c+k+1}-1))`.

The main result here is the **cut-set recursion** `NumV_rec`:

`q^{m+1} · NumV q (m+1) c j = (q^{m+1}-1)(q^{c+1}-1) · NumV q m (c+1) (j+1) + Jfac q (m+1) (j+1)`,

proved by an Abel summation whose term-by-term input is a pair of product identities.
Specialising `c = j = 0` collapses `NumV` to `(n+1)·Pfac q n`, which is what produces the
closed product form `d/(P(d)P(d-1))` of the vertex volume.
-/

namespace PGLQuotient

open Finset

section VolumeAlgebra

variable (q : ℝ)

-- [dropped: platform already declares Gpoly]
-- [dropped: platform already declares Jfac]
-- [dropped: platform already declares Pfac]
-- [dropped: platform already declares Cfac]
-- [dropped: platform already declares NumV]
-- [dropped: platform already declares DenV]
variable {q}

lemma Jfac_zero_right (r : ℕ) : Jfac q r 0 = Pfac q r := by
  unfold Jfac Pfac
  exact Finset.prod_congr rfl (fun s _ => by rw [Nat.add_zero])

lemma Jfac_succ (r j : ℕ) : Jfac q (r + 1) j = (q ^ (1 + j) - 1) * Jfac q r (j + 1) := by
  unfold Jfac
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  exact Finset.prod_congr rfl
    (fun s _ => by rw [show s + 1 + 1 + j = s + 1 + (j + 1) from by omega])

lemma Pfac_succ (n : ℕ) : Pfac q (n + 1) = Pfac q n * (q ^ (n + 1) - 1) := by
  unfold Pfac; rw [Finset.prod_range_succ]

lemma Cfac_succ (n c : ℕ) : Cfac q (n + 1) c = (q ^ (c + 1) - 1) * Cfac q n (c + 1) := by
  unfold Cfac
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  exact Finset.prod_congr rfl
    (fun k _ => by rw [show c + (k + 1) + 1 = c + 1 + k + 1 from by omega])

lemma Gpoly_succ_left (n i : ℕ) : Gpoly q (n + 1) (i + 1) = (q ^ (n + 1) - 1) * Gpoly q n i := by
  unfold Gpoly
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  exact Finset.prod_congr rfl (fun k _ => by rw [Nat.succ_sub_succ])

lemma Jfac_succ_right (r j : ℕ) : Jfac q (r + 1) j = Jfac q r j * (q ^ (r + 1 + j) - 1) := by
  unfold Jfac; rw [Finset.prod_range_succ]

lemma Gpoly_succ_right (n i : ℕ) : Gpoly q n (i + 1) = Gpoly q n i * (q ^ (n - i) - 1) := by
  unfold Gpoly; rw [Finset.prod_range_succ]

lemma Gpoly_zero (n : ℕ) : Gpoly q n 0 = 1 := by simp [Gpoly]

lemma Jfac_zero (j : ℕ) : Jfac q 0 j = 1 := by simp [Jfac]

/-- Beyond the diagonal the descending product vanishes. -/
lemma Gpoly_self_succ (m : ℕ) : Gpoly q m (m + 1) = 0 := by
  unfold Gpoly
  refine Finset.prod_eq_zero (Finset.self_mem_range_succ m) ?_
  simp

lemma Gpoly_mul_Jfac_zero {n i : ℕ} (hi : i ≤ n) :
    Gpoly q n i * Jfac q (n - i) 0 = Pfac q n := by
  induction i with
  | zero => rw [Gpoly_zero, one_mul, Nat.sub_zero, Jfac_zero_right]
  | succ i ih =>
      have hi' : i ≤ n := by omega
      have hstep : Jfac q (n - i) 0 = Jfac q (n - (i + 1)) 0 * (q ^ (n - i) - 1) := by
        rw [show n - i = (n - (i + 1)) + 1 from by omega, Jfac_succ_right, Nat.add_zero]
      have := ih hi'
      rw [hstep] at this
      rw [Gpoly_succ_right]
      calc Gpoly q n i * (q ^ (n - i) - 1) * Jfac q (n - (i + 1)) 0
          = Gpoly q n i * (Jfac q (n - (i + 1)) 0 * (q ^ (n - i) - 1)) := by ring
        _ = Pfac q n := this

lemma NumV_zero_right (n c : ℕ) : NumV q n c 0 = Pfac q n * ∑ i ∈ range (n + 1), q ^ (c * i) := by
  unfold NumV
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Gpoly_mul_Jfac_zero (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  ring

/-- The one-step difference identity behind the Abel summation. -/
lemma jfac_diff (t j : ℕ) :
    Jfac q t (j + 1) - (q ^ t - 1) * Jfac q (t - 1) (j + 1) = q ^ t * Jfac q t j := by
  cases t with
  | zero => simp [Jfac_zero]
  | succ t =>
      rw [Nat.add_sub_cancel, Jfac_succ_right t (j + 1), Jfac_succ t j]
      have hpow : q ^ (t + 1 + (j + 1)) = q ^ (t + 1) * q ^ (1 + j) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      ring

/-- The `i = 0` term of the Abel summation. -/
lemma abel_zero (m j : ℕ) :
    q ^ (m + 1) * (Gpoly q (m + 1) 0 * Jfac q (m + 1 - 0) j)
      = Jfac q (m + 1) (j + 1) - (q ^ (m + 1) - 1) * (Gpoly q m 0 * Jfac q (m - 0) (j + 1)) := by
  rw [Gpoly_zero, Gpoly_zero, one_mul, one_mul, Nat.sub_zero, Nat.sub_zero]
  have h := jfac_diff (q := q) (m + 1) j
  rw [Nat.add_sub_cancel] at h
  linarith

/-- The generic term of the Abel summation. -/
lemma abel_succ {m i : ℕ} (hi : i ≤ m) (j : ℕ) :
    q ^ (m + 1) * (Gpoly q (m + 1) (i + 1) * Jfac q (m + 1 - (i + 1)) j)
      = q ^ (i + 1) * (q ^ (m + 1) - 1) *
        (Gpoly q m i * Jfac q (m - i) (j + 1)
          - Gpoly q m (i + 1) * Jfac q (m - (i + 1)) (j + 1)) := by
  have hsub : m + 1 - (i + 1) = m - i := by omega
  have hsub2 : m - (i + 1) = (m - i) - 1 := by omega
  have hpow : q ^ (i + 1) * q ^ (m - i) = q ^ (m + 1) := by
    rw [← pow_add]; congr 1; omega
  have hcore := jfac_diff (q := q) (m - i) j
  have key : q ^ (m + 1) * Jfac q (m - i) j
      = q ^ (i + 1) * (Jfac q (m - i) (j + 1)
        - (q ^ (m - i) - 1) * Jfac q ((m - i) - 1) (j + 1)) := by
    rw [hcore, ← hpow]; ring
  rw [Gpoly_succ_left, Gpoly_succ_right, hsub, hsub2]
  linear_combination ((q ^ (m + 1) - 1) * Gpoly q m i) * key

/-- **The cut-set recursion.** -/
theorem NumV_rec (m c j : ℕ) :
    q ^ (m + 1) * NumV q (m + 1) c j
      = (q ^ (m + 1) - 1) * (q ^ (c + 1) - 1) * NumV q m (c + 1) (j + 1)
        + Jfac q (m + 1) (j + 1) := by
  set u : ℕ → ℝ := fun i => Gpoly q m i * Jfac q (m - i) (j + 1) with hu
  have hutop : u (m + 1) = 0 := by simp [hu, Gpoly_self_succ]
  have hNum : NumV q m (c + 1) (j + 1) = ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) * u i :=
    Finset.sum_congr rfl (fun i _ => by rw [hu])
  -- Abel summation: the shifted sum
  have hshift : (∑ i ∈ range (m + 1), q ^ (c * i) * q ^ i * u i) - u 0
      = ∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u (i + 1) := by
    rw [Finset.sum_range_succ' (fun i => q ^ (c * i) * q ^ i * u i) m,
      Finset.sum_range_succ (fun i => q ^ (c * (i + 1)) * q ^ (i + 1) * u (i + 1)) m, hutop]
    simp
  have hAC : (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u i)
        - (∑ i ∈ range (m + 1), q ^ (c * i) * q ^ i * u i)
      = (q ^ (c + 1) - 1) * ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) * u i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : q ^ (c * (i + 1)) * q ^ (i + 1) = q ^ ((c + 1) * i) * q ^ (c + 1) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    have h2 : q ^ (c * i) * q ^ i = q ^ ((c + 1) * i) := by
      rw [← pow_add]; congr 1; ring
    rw [h1, h2]; ring
  have hclaim : (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * (u i - u (i + 1))) - u 0
      = (q ^ (c + 1) - 1) * ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) * u i := by
    have hsplit : (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * (u i - u (i + 1)))
        = (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u i)
          - ∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u (i + 1) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit, ← hshift]
    linarith [hAC]
  -- the left-hand side, term by term
  have hL : q ^ (m + 1) * NumV q (m + 1) c j
      = ∑ i ∈ range (m + 1 + 1), q ^ (c * i) *
          (q ^ (m + 1) * (Gpoly q (m + 1) i * Jfac q (m + 1 - i) j)) := by
    unfold NumV
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hL, Finset.sum_range_succ' (fun i => q ^ (c * i) *
      (q ^ (m + 1) * (Gpoly q (m + 1) i * Jfac q (m + 1 - i) j))) (m + 1)]
  have hzero : q ^ (c * 0) * (q ^ (m + 1) * (Gpoly q (m + 1) 0 * Jfac q (m + 1 - 0) j))
      = Jfac q (m + 1) (j + 1) - (q ^ (m + 1) - 1) * u 0 := by
    rw [Nat.mul_zero, pow_zero, one_mul, abel_zero, hu]
  have hgen : ∀ i ∈ range (m + 1),
      q ^ (c * (i + 1)) * (q ^ (m + 1) * (Gpoly q (m + 1) (i + 1) * Jfac q (m + 1 - (i + 1)) j))
        = (q ^ (m + 1) - 1) * (q ^ (c * (i + 1)) * q ^ (i + 1) * (u i - u (i + 1))) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abel_succ hi' j, hu]
    ring
  rw [Finset.sum_congr rfl hgen, hzero, ← Finset.mul_sum, hNum]
  linear_combination (q ^ (m + 1) - 1) * hclaim

section Positivity

variable (hq : 1 < q)
include hq

lemma Jfac_pos (r j : ℕ) : 0 < Jfac q r j := by
  refine Finset.prod_pos (fun s _ => ?_)
  have : (1 : ℝ) < q ^ (s + 1 + j) := one_lt_pow₀ hq (by omega)
  linarith

lemma Pfac_pos (n : ℕ) : 0 < Pfac q n := by
  refine Finset.prod_pos (fun k _ => ?_)
  have : (1 : ℝ) < q ^ (k + 1) := one_lt_pow₀ hq (by omega)
  linarith

lemma Cfac_pos (n c : ℕ) : 0 < Cfac q n c := by
  refine Finset.prod_pos (fun k _ => ?_)
  have : (1 : ℝ) < q ^ (c + k + 1) := one_lt_pow₀ hq (by omega)
  linarith

lemma DenV_pos (n c j : ℕ) : 0 < DenV q n c j :=
  mul_pos (mul_pos (Jfac_pos hq _ _) (Pfac_pos hq _)) (Cfac_pos hq _ _)

lemma one_lt_pow_succ (k : ℕ) : (1:ℝ) < q ^ (k + 1) := one_lt_pow₀ hq (by omega)

/-- The closed form `NumV/DenV` solves the row-peeling recursion: this is the algebraic
content of the induction step. -/
lemma NumDen_step (m c j : ℕ) :
    (q ^ (m + 1) * (q ^ (j + 1) - 1))⁻¹ *
        (NumV q m (c + 1) (j + 1) / DenV q m (c + 1) (j + 1)
          + (q ^ ((m + 1) * (c + 1)) - 1)⁻¹ * (NumV q m (c + 1) 0 / DenV q m (c + 1) 0))
      = NumV q (m + 1) c j / DenV q (m + 1) c j := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hJ : 0 < Jfac q (m + 1) (j + 1) := Jfac_pos hq _ _
  have hP : 0 < Pfac q m := Pfac_pos hq _
  have hC : 0 < Cfac q m (c + 1) := Cfac_pos hq _ _
  have hm : (0:ℝ) < q ^ (m + 1) - 1 := by have := one_lt_pow_succ hq m; linarith
  have hc : (0:ℝ) < q ^ (c + 1) - 1 := by have := one_lt_pow_succ hq c; linarith
  have hj : (0:ℝ) < q ^ (j + 1) - 1 := by have := one_lt_pow_succ hq j; linarith
  have hmc : (0:ℝ) < q ^ ((m + 1) * (c + 1)) - 1 := by
    have : (1:ℝ) < q ^ ((m + 1) * (c + 1)) := one_lt_pow₀ hq (by positivity)
    linarith
  have hqm : (0:ℝ) < q ^ (m + 1) := pow_pos hq0 _
  have hDen1 : DenV q m (c + 1) (j + 1)
      = Jfac q (m + 1) (j + 1) * Pfac q m * Cfac q m (c + 1) := rfl
  have hDen0 : DenV q m (c + 1) 0
      = (Pfac q m * (q ^ (m + 1) - 1)) * Pfac q m * Cfac q m (c + 1) := by
    unfold DenV
    rw [Jfac_zero_right, Pfac_succ]
  have hDenS : DenV q (m + 1) c j
      = ((q ^ (1 + j) - 1) * Jfac q (m + 1) (j + 1)) * (Pfac q m * (q ^ (m + 1) - 1))
        * ((q ^ (c + 1) - 1) * Cfac q m (c + 1)) := by
    unfold DenV
    rw [Jfac_succ, Pfac_succ, Cfac_succ]
  have hN0 : NumV q m (c + 1) 0 * (q ^ (c + 1) - 1)
      = Pfac q m * (q ^ ((m + 1) * (c + 1)) - 1) := by
    rw [NumV_zero_right]
    have hs : ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) = ∑ i ∈ range (m + 1), (q ^ (c + 1)) ^ i :=
      Finset.sum_congr rfl (fun i _ => by rw [← pow_mul])
    rw [hs, mul_assoc, geom_sum_mul, ← pow_mul, Nat.mul_comm (c + 1) (m + 1)]
  have hrec := NumV_rec (q := q) m c j
  have hjj : q ^ (1 + j) = q ^ (j + 1) := by rw [Nat.add_comm]
  rw [hDen1, hDen0, hDenS, hjj]
  field_simp
  linear_combination (-(Pfac q m * (q ^ ((m + 1) * (c + 1)) - 1))) * hrec
    + Jfac q (m + 1) (j + 1) * hN0

end Positivity

end VolumeAlgebra

end PGLQuotient
section
open PGLQuotient
open Finset
variable (q : ℝ)
variable {q}

theorem solution (m c j : ℕ) :
    q ^ (m + 1) * NumV q (m + 1) c j
      = (q ^ (m + 1) - 1) * (q ^ (c + 1) - 1) * NumV q m (c + 1) (j + 1)
        + Jfac q (m + 1) (j + 1) :=
  PGLQuotient.NumV_rec m c j

end
