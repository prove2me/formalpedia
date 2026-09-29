-- Prove2me | solution 1 for LinearOptimization.polyhedron_linear_image
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T16:38:17.861226+00:00
-- url     : https://prove2.me/submissions/a55db916-3303-44bf-9ab6-bf32fa00f39f

import Theorems.Thm_LinearOptimization_polyhedron_projection
import Mathlib.Algebra.BigOperators.Fin

open Matrix

namespace LinearOptimization

def graphMatrix {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ) :
    Matrix (Fin (m + (p + (p + 1)))) (Fin (p + n)) ℝ :=
  fun i j =>
    Fin.addCases
      (fun r => Fin.addCases (fun _ => 0) (fun c => A r c) j)
      (fun i' => Fin.addCases
        (fun r => Fin.addCases (fun q => if q = r then -1 else 0) (fun c => M r c) j)
        (fun q => Fin.lastCases
          0
          (fun r => Fin.addCases (fun q => if q = r then 1 else 0) (fun c => -M r c) j)
          q)
        i')
      i

def graphRhs {m p : ℕ} (b : Fin m → ℝ) : Fin (m + (p + (p + 1))) → ℝ :=
  Fin.addCases b (fun _ => 0)

theorem graph_mulVec_orig {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) (r : Fin m) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.castAdd (p + (p + 1)) r) = A.mulVec x r := by
  simp [graphMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

theorem graph_mulVec_lower {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) (r : Fin p) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.natAdd m (Fin.castAdd (p + 1) r)) = M.mulVec x r - y r := by
  simp [graphMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  ring

theorem graph_mulVec_upper {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) (r : Fin p) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.natAdd m (Fin.natAdd p r.castSucc)) = y r - M.mulVec x r := by
  simp [graphMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  ring

theorem graph_mulVec_dummy {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.natAdd m (Fin.natAdd p (Fin.last p))) = 0 := by
  have hrow : graphMatrix A M (Fin.natAdd m (Fin.natAdd p (Fin.last p))) =
      (fun _ => 0) := by
    funext j
    unfold graphMatrix
    rw [Fin.addCases_right, Fin.addCases_right, Fin.lastCases_last]
  change dotProduct (graphMatrix A M (Fin.natAdd m (Fin.natAdd p (Fin.last p))))
      (Fin.append y x) = 0
  rw [hrow]
  simp [dotProduct]

theorem graph_mem_iff {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : Matrix (Fin p) (Fin n) ℝ) (y : Fin p → ℝ) (x : Fin n → ℝ) :
    Fin.append y x ∈ polyhedron (graphMatrix A M) (graphRhs b) ↔
      x ∈ polyhedron A b ∧ y = M.mulVec x := by
  constructor
  · intro h
    constructor
    · intro r
      simpa [graphRhs, graph_mulVec_orig] using
        h (Fin.castAdd (p + (p + 1)) r)
    · funext r
      have hlo := h (Fin.natAdd m (Fin.castAdd (p + 1) r))
      simp [graphRhs, graph_mulVec_lower] at hlo
      have hhi := h (Fin.natAdd m (Fin.natAdd p r.castSucc))
      simp [graphRhs, graph_mulVec_upper] at hhi
      linarith
  · rintro ⟨hx, rfl⟩ i
    refine Fin.addCases
      (motive := fun i => graphRhs b i ≤
        (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x) i)
      (fun r => by simpa [graphRhs, graph_mulVec_orig] using hx r)
      (fun i' => by
        refine Fin.addCases
          (motive := fun i' => graphRhs b (Fin.natAdd m i') ≤
            (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x) (Fin.natAdd m i'))
          (fun r => by simp [graphRhs, graph_mulVec_lower])
          (fun q => by
            refine Fin.lastCases
              (motive := fun q => graphRhs b (Fin.natAdd m (Fin.natAdd p q)) ≤
                (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x)
                  (Fin.natAdd m (Fin.natAdd p q)))
              (by
                change graphRhs b (Fin.last (m + (p + p))) ≤
                  (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x)
                    (Fin.last (m + (p + p)))
                have hidx : Fin.last (m + (p + p)) =
                    Fin.natAdd m (Fin.natAdd p (Fin.last p)) := by
                  ext
                  simp
                rw [hidx]
                have hbzero : graphRhs b (Fin.natAdd m (Fin.natAdd p (Fin.last p))) = 0 := by
                  simp only [graphRhs, Fin.addCases_right]
                rw [hbzero, graph_mulVec_dummy]
                )
              (fun r => by simp [graphRhs, graph_mulVec_upper]) q)
          i')
      i

end LinearOptimization

theorem solution {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : Matrix (Fin p) (Fin n) ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin p) ℝ) (b' : Fin m' → ℝ),
      M.mulVec '' LinearOptimization.polyhedron A b =
        LinearOptimization.polyhedron A' b' := by
  obtain ⟨m', A', b', hproj⟩ :=
    LinearOptimization.polyhedron_projection
      (LinearOptimization.graphMatrix A M) (LinearOptimization.graphRhs b)
  refine ⟨m', A', b', ?_⟩
  rw [← hproj]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (LinearOptimization.graph_mem_iff A b M (M.mulVec x) x).2 ⟨hx, rfl⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hxp, hy⟩ := (LinearOptimization.graph_mem_iff A b M y x).1 hx
    exact ⟨x, hxp, hy.symm⟩
