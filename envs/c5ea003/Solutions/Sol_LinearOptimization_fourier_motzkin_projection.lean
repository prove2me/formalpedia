-- Prove2me | solution 1 for LinearOptimization.fourier_motzkin_projection
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T15:53:58.42601+00:00
-- url     : https://prove2.me/submissions/0e54f204-77df-47e9-beb0-b606c007b9bc

import Definitions.Def_FourierMotzkinStep
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

open Matrix Finset

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) :
    LinearOptimization.fourierMotzkinEliminate A b =
      (fun x : Fin (n + 1) → ℝ => fun l : Fin n => x l.castSucc) ''
        LinearOptimization.polyhedron A b := by
  classical
  ext y
  constructor
  · intro hy
    let pos : Finset (Fin m) :=
      Finset.univ.filter (fun i => 0 < A i (Fin.last n))
    let neg : Finset (Fin m) :=
      Finset.univ.filter (fun i => A i (Fin.last n) < 0)
    by_cases hp : pos.Nonempty
    · obtain ⟨i, hi, hiMax⟩ :=
        Finset.exists_max_image pos
          (fun r => LinearOptimization.fourierMotzkinBound A b r y) hp
      have hai : 0 < A i (Fin.last n) := (Finset.mem_filter.mp hi).2
      refine ⟨Fin.snoc y (LinearOptimization.fourierMotzkinBound A b i y), ?_, ?_⟩
      · intro r
        change b r ≤ ∑ q : Fin (n + 1), A r q *
          (Fin.snoc y (LinearOptimization.fourierMotzkinBound A b i y) :
            Fin (n + 1) → ℝ) q
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        simp only [LinearOptimization.fourierMotzkinBound]
        by_cases har : 0 < A r (Fin.last n)
        · have hr : r ∈ pos := Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩
          have hbound := hiMax r hr
          simp only [LinearOptimization.fourierMotzkinBound] at hbound
          rw [div_le_iff₀ har] at hbound
          nlinarith
        · by_cases har0 : A r (Fin.last n) = 0
          · have hzero := hy.1 r har0
            simp only [har0, zero_mul, add_zero]
            exact hzero
          · have harneg : A r (Fin.last n) < 0 :=
              lt_of_le_of_ne (le_of_not_gt har) har0
            have hbound := hy.2 i r hai harneg
            simp only [LinearOptimization.fourierMotzkinBound] at hbound
            rw [le_div_iff_of_neg harneg] at hbound
            nlinarith
      · funext l
        simp
    · by_cases hn : neg.Nonempty
      · obtain ⟨j, hj, hjMin⟩ :=
          Finset.exists_min_image neg
            (fun r => LinearOptimization.fourierMotzkinBound A b r y) hn
        have haj : A j (Fin.last n) < 0 := (Finset.mem_filter.mp hj).2
        refine ⟨Fin.snoc y (LinearOptimization.fourierMotzkinBound A b j y), ?_, ?_⟩
        · intro r
          change b r ≤ ∑ q : Fin (n + 1), A r q *
            (Fin.snoc y (LinearOptimization.fourierMotzkinBound A b j y) :
              Fin (n + 1) → ℝ) q
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          simp only [LinearOptimization.fourierMotzkinBound]
          by_cases har : 0 < A r (Fin.last n)
          · exact (hp ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩⟩).elim
          · by_cases har0 : A r (Fin.last n) = 0
            · have hzero := hy.1 r har0
              simp only [har0, zero_mul, add_zero]
              exact hzero
            · have harneg : A r (Fin.last n) < 0 :=
                lt_of_le_of_ne (le_of_not_gt har) har0
              have hr : r ∈ neg := Finset.mem_filter.mpr ⟨Finset.mem_univ r, harneg⟩
              have hbound := hjMin r hr
              simp only [LinearOptimization.fourierMotzkinBound] at hbound
              rw [le_div_iff_of_neg harneg] at hbound
              nlinarith
        · funext l
          simp
      · refine ⟨Fin.snoc y 0, ?_, ?_⟩
        · intro r
          change b r ≤ ∑ q : Fin (n + 1), A r q *
            (Fin.snoc y 0 : Fin (n + 1) → ℝ) q
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
          have hnotpos : ¬ 0 < A r (Fin.last n) := by
            intro har
            exact hp ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩⟩
          have hnotneg : ¬ A r (Fin.last n) < 0 := by
            intro har
            exact hn ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩⟩
          have har0 : A r (Fin.last n) = 0 :=
            le_antisymm (le_of_not_gt hnotpos) (le_of_not_gt hnotneg)
          exact hy.1 r har0
        · funext l
          simp
  · rintro ⟨x, hx, rfl⟩
    constructor
    · intro k hk
      have h := hx k
      change b k ≤ ∑ q : Fin (n + 1), A k q * x q at h
      rw [Fin.sum_univ_castSucc] at h
      simpa [hk] using h
    · intro i j hi hj
      have hfi := hx i
      have hfj := hx j
      change b i ≤ ∑ q : Fin (n + 1), A i q * x q at hfi
      change b j ≤ ∑ q : Fin (n + 1), A j q * x q at hfj
      rw [Fin.sum_univ_castSucc] at hfi hfj
      have hLower :
          LinearOptimization.fourierMotzkinBound A b i
              (fun l : Fin n => x l.castSucc) ≤ x (Fin.last n) := by
        simp only [LinearOptimization.fourierMotzkinBound]
        rw [div_le_iff₀ hi]
        linarith
      have hUpper :
          x (Fin.last n) ≤ LinearOptimization.fourierMotzkinBound A b j
              (fun l : Fin n => x l.castSucc) := by
        simp only [LinearOptimization.fourierMotzkinBound]
        rw [le_div_iff_of_neg hj]
        linarith
      exact hLower.trans hUpper
