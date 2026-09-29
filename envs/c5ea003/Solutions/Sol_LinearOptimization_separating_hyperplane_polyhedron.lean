-- Prove2me | solution 1 for LinearOptimization.separating_hyperplane_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:44:33.126541+00:00
-- url     : https://prove2.me/submissions/77238986-73b7-4676-8ac8-442a64539b58

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Matrix.Mul

open Matrix

theorem solution {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : S.Nonempty) (hclosed : IsClosed S) (hconv : Convex ℝ S)
    (xstar : Fin n → ℝ) (hx : xstar ∉ S) :
    ∃ c : Fin n → ℝ, ∀ x ∈ S, c ⬝ᵥ xstar < c ⬝ᵥ x := by
  classical
  obtain ⟨f, u, hstar, hf⟩ :=
    geometric_hahn_banach_point_closed hconv hclosed hx
  let c : Fin n → ℝ := fun i ↦ f (Pi.single i 1)
  have hdot (z : Fin n → ℝ) : c ⬝ᵥ z = f z := by
    calc
      c ⬝ᵥ z = ∑ i : Fin n, f (z i • Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [c, mul_comm]
      _ = f (∑ i : Fin n, z i • Pi.single i 1) := by
        rw [map_sum]
      _ = f z := by
        congr 1
        funext i
        simp [Pi.single_apply]
  refine ⟨c, fun x hxS ↦ ?_⟩
  have hsep : f xstar < f x := hstar.trans (hf x hxS)
  simpa [hdot] using hsep
