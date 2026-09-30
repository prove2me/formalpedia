-- Prove2me | solution 1 for Hirsch.polynomial_edge_refinement_of_circuit_walks
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T23:03:31.816917+00:00
-- url     : https://prove2.me/submissions/1a375782-7537-44cf-b5f8-4a516e41b48a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Hirsch_dimension_three_bound
import Theorems.Thm_Hirsch_polynomial_edge_refinement_of_circuit_walks_dim_ge_four

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Hirsch

/-- Stationary padding: `DiamLE` is monotone in the walk length. -/
theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {m L : ℕ} (h : m ≤ L) (hP : DiamLE P m) : DiamLE P L := by
  intro u hu v hv
  obtain ⟨w, hw0, hwm, hs⟩ := hP u hu v hv
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

/-- From a `DiamLE` bound, extract a padded walk of any larger exact length. -/
theorem padded_walk_of_diamLE {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {m B : ℕ} (h : m ≤ B) (hP : DiamLE P m)
    {u v : E} (hu : u ∈ Set.extremePoints ℝ P) (hv : v ∈ Set.extremePoints ℝ P) :
    ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) :=
  diamLE_mono P h hP u hu v hv

/-- Length-zero circuit walks have equal endpoints, so a length-zero graph walk. -/
theorem zero_circuit_walk_stationary {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hwalk : RowCircuitWalk a b 0 u v) :
    u = v := by
  obtain ⟨w, hw0, hwL, _, _⟩ := hwalk
  exact hw0.symm.trans hwL

/-- Sketch: the `d ≤ 3` case is Klee's theorem; the remaining content is
high-dimensional circuit-to-edge refinement. -/
theorem solution :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
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
    Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four
  refine ⟨Ch + 1, kh + 1, ?_⟩
  intro d n a b hbd hirr hstrict u hu v hv L hwalk
  by_cases hL0 : L = 0
  · subst hL0
    have huv : u = v := zero_circuit_walk_stationary a b hwalk
    refine ⟨fun _ => u, rfl, ?_, ?_⟩
    · simp [huv]
    · intro _ _
      exact Or.inl rfl
  · have hLpos : 1 ≤ L := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hL0)
    by_cases hd : d ≤ 3
    · have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
      have hdiam : DiamLE (Hpoly a b) (n - d) :=
        dimension_three_bound d n hd a b hne hbd
      let B : ℕ := (Ch + 1) * (n + d) ^ (kh + 1) * L
      have hlen : n - d ≤ B := by
        have hnd : n - d ≤ n + d := (Nat.sub_le n d).trans (Nat.le_add_right n d)
        have hbase : n + d ≤ (n + d) ^ (kh + 1) := by
          by_cases hz : n + d = 0
          · simp [hz]
          · have hpos : 1 ≤ n + d := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hz)
            exact Nat.le_self_pow (Nat.succ_ne_zero kh) (n + d)
        have hC : n + d ≤ (Ch + 1) * (n + d) ^ (kh + 1) := by
          have h1 : 1 ≤ Ch + 1 := Nat.succ_le_succ (Nat.zero_le _)
          calc
            n + d ≤ (n + d) ^ (kh + 1) := hbase
            _ = 1 * (n + d) ^ (kh + 1) := by ring
            _ ≤ (Ch + 1) * (n + d) ^ (kh + 1) :=
              Nat.mul_le_mul_right _ h1
        have : n + d ≤ B := by
          calc
            n + d ≤ (Ch + 1) * (n + d) ^ (kh + 1) := hC
            _ = (Ch + 1) * (n + d) ^ (kh + 1) * 1 := by ring
            _ ≤ (Ch + 1) * (n + d) ^ (kh + 1) * L :=
              Nat.mul_le_mul_left _ hLpos
        exact hnd.trans this
      exact padded_walk_of_diamLE (Hpoly a b) hlen hdiam hu hv
    · have hd4 : 4 ≤ d := by omega
      obtain ⟨w, hw0, hwB, hstep⟩ :=
        hhigh d n a b hd4 hbd hirr hstrict u hu v hv L hwalk
      let B0 : ℕ := Ch * (n + d) ^ kh * L
      let B : ℕ := (Ch + 1) * (n + d) ^ (kh + 1) * L
      have hBB : B0 ≤ B := by
        have hpos : n + d > 0 := by omega
        have hpow : (n + d) ^ kh ≤ (n + d) ^ (kh + 1) :=
          Nat.pow_le_pow_right hpos (Nat.le_succ kh)
        have hC : Ch ≤ Ch + 1 := Nat.le_succ _
        have hmul1 : Ch * (n + d) ^ kh ≤ (Ch + 1) * (n + d) ^ (kh + 1) :=
          Nat.mul_le_mul hC hpow
        exact Nat.mul_le_mul_right L hmul1
      refine ⟨fun j => w (min j B0), ?_, ?_, ?_⟩
      · simpa [Nat.min_eq_left (Nat.zero_le _)] using hw0
      · change w (min B B0) = v
        rw [Nat.min_eq_right hBB]
        exact hwB
      · intro j hj
        by_cases hjB : j < B0
        · have hjle : j ≤ B0 := Nat.le_of_lt hjB
          have hj1le : j + 1 ≤ B0 := by omega
          simpa [Nat.min_eq_left hjle, Nat.min_eq_left hj1le] using hstep j hjB
        · have hBj : B0 ≤ j := by omega
          have hBj1 : B0 ≤ j + 1 := by omega
          exact Or.inl (by simp [Nat.min_eq_right hBj, Nat.min_eq_right hBj1])

#print axioms solution
