-- Prove2me | solution 2 for Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T02:08:31.237037+00:00
-- url     : https://prove2.me/submissions/bd09f3a4-248e-47f1-8bfe-68ff2bc61cb5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Hirsch_common_face_sequence_route_bound_of_dim_le_three
import Theorems.Thm_Hirsch_polynomial_edge_refinement_of_circuit_walks_of_high_carrier

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Hirsch HirschCommonFace

theorem diamLE_pad_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {m B : ℕ} (h : m ≤ B)
    {u v : E} (_hu : u ∈ Set.extremePoints ℝ P) (_hv : v ∈ Set.extremePoints ℝ P)
    (hP : ∃ w : ℕ → E, w 0 = u ∧ w m = v ∧
      ∀ j < m, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  obtain ⟨w, hw0, hwm, hs⟩ := hP
  refine ⟨fun i => w (min i m), ?_, ?_, ?_⟩
  · simp [hw0]
  · simp [min_eq_right h, hwm]
  · intro i hi
    by_cases h1 : i + 1 ≤ m
    · have hi' : i < m := Nat.lt_of_succ_le h1
      have hmin_i : min i m = i := min_eq_left (Nat.le_of_lt hi')
      have hmin_i1 : min (i + 1) m = i + 1 := min_eq_left h1
      simpa [hmin_i, hmin_i1] using hs i hi'
    · have hmi : min i m = m := by omega
      have hmi1 : min (i + 1) m = m := by omega
      exact Or.inl (by simp [hmi, hmi1])

theorem solution :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      4 ≤ d →
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      Hirsch.RowPresentationIrredundant a b → Hirsch.StrictlyFeasibleRows a b →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ L : ℕ, Hirsch.RowCircuitWalk a b L u v →
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k * L) = v ∧
          ∀ j < C * (n + d) ^ k * L,
            w j = w (j + 1) ∨
              Hirsch.Adj (Hirsch.Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨Ch, kh, hhigh⟩ :=
    Hirsch.polynomial_edge_refinement_of_circuit_walks_of_high_carrier
  refine ⟨Ch + 1, kh + 1, ?_⟩
  intro d n a b hd4 hbd hirr hstrict u hu v hv L hwalk
  obtain ⟨wcirc, hw0, hwL, hfeas, hstep⟩ := hwalk
  by_cases hAll : ∀ k : Fin L,
      commonFaceDim a b (wcirc k.val) (wcirc (k.val + 1)) ≤ 3
  · have hdim : ∀ k < L,
        commonFaceDim a b (wcirc k) (wcirc (k + 1)) ≤ 3 := by
      intro k hk
      exact hAll ⟨k, hk⟩
    have hlow :=
      common_face_sequence_route_bound_of_dim_le_three a b hbd
        wcirc L hfeas (by simpa [hw0] using hu) (by simpa [hwL] using hv) hdim
    let B : ℕ := (Ch + 1) * (n + d) ^ (kh + 1) * L
    have hlen : n * L ≤ B := by
      have hn : n ≤ n + d := Nat.le_add_right n d
      have hbase : n + d ≤ (n + d) ^ (kh + 1) :=
        Nat.le_self_pow (Nat.succ_ne_zero kh) (n + d)
      have hC : n + d ≤ (Ch + 1) * (n + d) ^ (kh + 1) :=
        hbase.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos Ch))
      calc
        n * L ≤ (n + d) * L := Nat.mul_le_mul_right L hn
        _ ≤ (Ch + 1) * (n + d) ^ (kh + 1) * L :=
          Nat.mul_le_mul_right L hC
    exact diamLE_pad_walk hlen hu hv (by
      simpa [hw0, hwL] using hlow)
  · have hsome : ∃ j < L, 3 < commonFaceDim a b (wcirc j) (wcirc (j + 1)) := by
      have : ¬∀ k : Fin L,
          commonFaceDim a b (wcirc k.val) (wcirc (k.val + 1)) ≤ 3 := hAll
      push Not at this
      obtain ⟨k, hk⟩ := this
      exact ⟨k.val, k.isLt, hk⟩
    obtain ⟨q, hq0, hqB, hstepq⟩ :=
      hhigh d n a b hd4 hbd hirr hstrict u hu v hv L wcirc hw0 hwL hfeas hstep hsome
    let B0 : ℕ := Ch * (n + d) ^ kh * L
    let B : ℕ := (Ch + 1) * (n + d) ^ (kh + 1) * L
    have hBB : B0 ≤ B := by
      have hpos : n + d > 0 := by omega
      have hpow : (n + d) ^ kh ≤ (n + d) ^ (kh + 1) :=
        Nat.pow_le_pow_right hpos (Nat.le_succ kh)
      exact Nat.mul_le_mul_right L (Nat.mul_le_mul (Nat.le_succ Ch) hpow)
    exact diamLE_pad_walk hBB hu hv ⟨q, hq0, hqB, hstepq⟩
