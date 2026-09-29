-- Prove2me | solution 1 for LinearOptimization.polyhedron_projection
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T16:28:46.339068+00:00
-- url     : https://prove2.me/submissions/cde0a5c9-4759-48ae-8b77-43835e3f926f

import Theorems.Thm_LinearOptimization_fourier_motzkin_projection
import Theorems.Thm_LinearOptimization_fourier_motzkin_eliminate_is_polyhedron

theorem solution {m n k : ℕ}
    (A : Matrix (Fin m) (Fin (n + k)) ℝ) (b : Fin m → ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      {x : Fin n → ℝ | ∃ y : Fin k → ℝ,
          Fin.append x y ∈ LinearOptimization.polyhedron A b} =
        LinearOptimization.polyhedron A' b' := by
  classical
  induction k generalizing m with
  | zero =>
      refine ⟨m, A, b, ?_⟩
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have hy0 : y = Fin.elim0 := Subsingleton.elim _ _
        subst y
        simpa using hy
      · intro hx
        exact ⟨Fin.elim0, by simpa using hx⟩
  | succ k ih =>
      obtain ⟨m₁, A₁, b₁, hpoly⟩ :=
        LinearOptimization.fourier_motzkin_eliminate_is_polyhedron A b
      have hlast :
          (fun z : Fin (n + k + 1) → ℝ => fun l : Fin (n + k) => z l.castSucc) ''
              LinearOptimization.polyhedron A b =
            LinearOptimization.polyhedron A₁ b₁ := by
        calc
          _ = LinearOptimization.fourierMotzkinEliminate A b :=
            (LinearOptimization.fourier_motzkin_projection A b).symm
          _ = _ := hpoly
      obtain ⟨m₂, A₂, b₂, hrest⟩ := ih A₁ b₁
      refine ⟨m₂, A₂, b₂, ?_⟩
      rw [← hrest]
      ext x
      constructor
      · rintro ⟨ys, hys⟩
        refine ⟨Fin.init ys, ?_⟩
        rw [← hlast]
        refine ⟨Fin.snoc (Fin.append x (Fin.init ys)) (ys (Fin.last k)), ?_, ?_⟩
        · rw [← Fin.append_snoc, Fin.snoc_init_self]
          exact hys
        · funext l
          simp
      · rintro ⟨y, hy⟩
        have himage : Fin.append x y ∈
            (fun z : Fin (n + k + 1) → ℝ => fun l : Fin (n + k) => z l.castSucc) ''
              LinearOptimization.polyhedron A b := by
          rw [hlast]
          exact hy
        rcases himage with ⟨z, hz, hzproj⟩
        refine ⟨Fin.snoc y (z (Fin.last (n + k))), ?_⟩
        have hzinit : Fin.init z = Fin.append x y := by
          exact hzproj
        rw [Fin.append_snoc, ← hzinit]
        have hsnoc : Fin.snoc (Fin.init z) (z (Fin.last (n + k))) = z := by
          apply Fin.snoc_init_self
        rw [hsnoc]
        exact hz
