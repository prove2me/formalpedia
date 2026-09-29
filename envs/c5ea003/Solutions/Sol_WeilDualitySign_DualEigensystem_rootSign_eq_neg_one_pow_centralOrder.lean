-- Prove2me | solution 1 for WeilDualitySign.DualEigensystem.rootSign_eq_neg_one_pow_centralOrder
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:49:43.21436+00:00
-- url     : https://prove2.me/submissions/34e75814-e5af-47b7-9151-eacfbffd3dda

import Mathlib
import Definitions.Def_Applications_WeilDualitySign_CentralParity
import Definitions.Def_Applications_WeilDualitySign_EigenvalueModel

open Finset WeilDualitySign in
theorem solution {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : DualEigensystem K ι) (hchar : (-1 : K) ≠ 1) :
    E.rootSign = (-1 : K) ^ E.centralOrder := by
  classical
  have hQ := E.Q_ne_zero
  have hQne : E.Q ≠ -E.Q := by
    intro h
    apply hchar
    have h2 : (2 : K) * E.Q = 0 := by linear_combination h
    have h2' : (2 : K) = 0 := (mul_eq_zero.1 h2).resolve_right hQ
    linear_combination (-1 : K) * h2'
  -- normalised eigenvalues and the central-sign indicator
  let s : ι → K := fun i => (-1) * E.α i * E.Q⁻¹
  let t : ι → K := fun i => if E.α i = E.Q then -1 else 1
  have hdual : ∀ i, E.α i = E.Q → E.α (E.σ i) = E.Q := by
    intro i hi
    have h := E.duality i
    rw [hi] at h
    have h' : E.Q * (E.α (E.σ i) - E.Q) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hQ)
  have htσ : ∀ i, t (E.σ i) = t i := by
    intro i
    by_cases hi : E.α i = E.Q
    · simp only [t, if_pos (hdual i hi), if_pos hi]
    · have hn : ¬ E.α (E.σ i) = E.Q := fun h => hi (by
        have := hdual (E.σ i) h
        rwa [E.σ_involutive] at this)
      simp only [t, if_neg hn, if_neg hi]
  have ht2 : ∀ i, t i * t i = 1 := fun i => by
    simp only [t]
    split_ifs <;> ring
  have hss : ∀ i, s i * s (E.σ i) = 1 := by
    intro i
    simp only [s]
    field_simp
    linear_combination E.duality i
  -- pair each index with its dual
  have hprod : ∏ i, (s i * t i) = 1 := by
    refine Finset.prod_involution (fun i _ => E.σ i) (fun i _ => ?_) (fun i _ hne => ?_)
      (fun i _ => Finset.mem_univ _) (fun i _ => E.σ_involutive i)
    · rw [htσ i]
      calc s i * t i * (s (E.σ i) * t i) = (s i * s (E.σ i)) * (t i * t i) := by ring
        _ = 1 := by rw [hss i, ht2 i, one_mul]
    · intro hfix
      have hfix' : E.σ i = i := hfix
      apply hne
      have hsq : E.α i * E.α i = E.Q ^ 2 := by
        have h := E.duality i
        rwa [hfix'] at h
      have hfac : (E.α i - E.Q) * (E.α i + E.Q) = 0 := by linear_combination hsq
      rcases mul_eq_zero.1 hfac with h | h
      · have hi : E.α i = E.Q := sub_eq_zero.1 h
        simp only [s, t, if_pos hi, hi]
        field_simp
      · have hi : E.α i = -E.Q := eq_neg_of_add_eq_zero_left h
        have hi' : ¬ E.α i = E.Q := fun h' => hQne (h'.symm.trans hi)
        simp only [s, t, if_neg hi', hi]
        field_simp
  have hT : ∏ i, t i = (-1 : K) ^ E.centralOrder := by
    simp only [t]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rfl
  have hS : E.rootSign = ∏ i, s i := by
    simp only [s, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    rw [DualEigensystem.rootSign, DualEigensystem.deg, div_eq_mul_inv, inv_pow]
  have htt : (∏ i, t i) * (∏ i, t i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => ht2 i
  rw [Finset.prod_mul_distrib] at hprod
  rw [hS, ← hT]
  calc ∏ i, s i = (∏ i, s i) * ((∏ i, t i) * (∏ i, t i)) := by rw [htt, mul_one]
    _ = ((∏ i, s i) * (∏ i, t i)) * (∏ i, t i) := by ring
    _ = ∏ i, t i := by rw [hprod, one_mul]
