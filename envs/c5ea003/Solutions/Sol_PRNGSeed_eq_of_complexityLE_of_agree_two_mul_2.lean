-- Prove2me | solution 2 for PRNGSeed.eq_of_complexityLE_of_agree_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:31:25.071482+00:00
-- url     : https://prove2.me/submissions/d2c9c19f-0046-4c46-aea8-a645588c8168

import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
open Finset Polynomial PRNGSeed in
theorem solution {F : Type*} [CommRing F] [Nontrivial F] [NoZeroDivisors F] {L : ℕ}
    {x y : ℕ → F}
    (hx : ComplexityLE L x) (hy : ComplexityLE L y)
    (hagree : ∀ i : ℕ, i < 2 * L → x i = y i) : x = y := by
  -- polynomials act on streams through the shift operator
  let S : Module.End F (ℕ → F) := shift
  have hpow : ∀ (i : ℕ) (z : ℕ → F) (n : ℕ), (S ^ i) z n = z (n + i) := by
    intro i
    induction i with
    | zero => intro z n; rfl
    | succ i ih =>
      intro z n
      rw [pow_succ, Module.End.mul_apply, ih]
      show z (n + i + 1) = z (n + (i + 1))
      rw [add_assoc]
  have haeval : ∀ (P : F[X]) (z : ℕ → F) (n : ℕ),
      (aeval S P) z n = ∑ i ∈ range (P.natDegree + 1), P.coeff i * z (n + i) := by
    intro P z n
    rw [aeval_eq_sum_range, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply]
    refine sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.smul_apply, Pi.smul_apply, hpow, smul_eq_mul]
  -- a stream obeying the recurrence is killed by its characteristic polynomial
  have hkill : ∀ (c : Fin L → F) (z : ℕ → F), IsLinRec L c z →
      aeval S (LinearRecurrence.charPoly ⟨L, c⟩) z = 0 := by
    intro c z hz
    funext n
    simp only [LinearRecurrence.charPoly, map_sub, map_sum, aeval_monomial, LinearMap.sub_apply,
      LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Pi.sub_apply, Pi.smul_apply, one_smul, smul_eq_mul, Pi.zero_apply]
    rw [hpow, hz n, sub_eq_zero]
    exact sum_congr rfl (fun i _ => by rw [hpow])
  obtain ⟨c, hc⟩ := hx
  obtain ⟨d, hd⟩ := hy
  set p := LinearRecurrence.charPoly (⟨L, c⟩ : LinearRecurrence F) with hp
  set q := LinearRecurrence.charPoly (⟨L, d⟩ : LinearRecurrence F) with hq
  have hpm : p.Monic := LinearRecurrence.charPoly_monic _
  have hqm : q.Monic := LinearRecurrence.charPoly_monic _
  have hpd : p.natDegree = L :=
    natDegree_eq_of_degree_eq_some (LinearRecurrence.charPoly_degree_eq_order _)
  have hqd : q.natDegree = L :=
    natDegree_eq_of_degree_eq_some (LinearRecurrence.charPoly_degree_eq_order _)
  -- the difference is killed by `p q`, monic of degree `2L`
  have hz : aeval S (p * q) (x - y) = 0 := by
    have h1 : aeval S (p * q) x = 0 := by
      rw [mul_comm, map_mul, Module.End.mul_apply, hkill c x hc, map_zero]
    have h2 : aeval S (p * q) y = 0 := by
      rw [map_mul, Module.End.mul_apply, hkill d y hd, map_zero]
    rw [map_sub, h1, h2, sub_zero]
  have hPm : (p * q).Monic := hpm.mul hqm
  have hPd : (p * q).natDegree = 2 * L := by rw [hpm.natDegree_mul hqm, hpd, hqd]; ring
  -- so `z = x − y` satisfies a monic recurrence of order `2L` and vanishes initially
  have hrec : ∀ n, (x - y) (n + 2 * L)
      = -∑ i ∈ range (2 * L), (p * q).coeff i * (x - y) (n + i) := by
    intro n
    have := congrFun hz n
    rw [haeval, hPd, sum_range_succ, ← hPd, hPm.coeff_natDegree, hPd, one_mul] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact this
  have hzero : ∀ n, (x - y) n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < 2 * L
      · simp [hagree n hn]
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 * L := ⟨n - 2 * L, by omega⟩
        rw [hrec k, neg_eq_zero]
        exact sum_eq_zero (fun i hi => by
          rw [ih (k + i) (by rw [mem_range] at hi; omega), mul_zero])
  funext n
  exact sub_eq_zero.mp (hzero n)
