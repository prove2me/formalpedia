-- Prove2me | solution 1 for PGLQuotient.NumDen_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:18:29.052044+00:00
-- url     : https://prove2.me/submissions/eec3afb2-1b09-4bc6-9078-41e9145ed0ec

-- Sol generated from Algebra/PGLQuotient/VolumeAlgebra.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra
import Theorems.Thm_PGLQuotient_Jfac_zero_right
import Theorems.Thm_PGLQuotient_NumV_rec
import Theorems.Thm_PGLQuotient_NumV_zero_right
import Theorems.Thm_PGLQuotient_Pfac_pos

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

open PGLQuotient

open Finset


variable (q : ℝ)







variable {q}


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














variable (hq : 1 < q)
include hq

lemma Jfac_pos (r j : ℕ) : 0 < Jfac q r j := by
  refine Finset.prod_pos (fun s _ => ?_)
  have : (1 : ℝ) < q ^ (s + 1 + j) := one_lt_pow₀ hq (by omega)
  linarith


lemma Cfac_pos (n c : ℕ) : 0 < Cfac q n c := by
  refine Finset.prod_pos (fun k _ => ?_)
  have : (1 : ℝ) < q ^ (c + k + 1) := one_lt_pow₀ hq (by omega)
  linarith


lemma one_lt_pow_succ (k : ℕ) : (1:ℝ) < q ^ (k + 1) := one_lt_pow₀ hq (by omega)





open PGLQuotient in
theorem solution(m c j : ℕ) :
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
