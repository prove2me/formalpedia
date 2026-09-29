-- Prove2me | solution 1 for TropicalLA.IsTropEigen.cycle_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:16:42.101986+00:00
-- url     : https://prove2.me/submissions/d0279e68-0215-4316-aafb-01359557c8ca

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}
    (h : IsTropEigen A lam v) {m : ℕ} {c : ℕ → ι} (hc : c m = c 0) :
    pathWeight A c m ≤ m * lam := by
  -- every transition is subinvariant: `A i j + v j ≤ lam + v i`
  have hle : ∀ i j : ι, A i j + v j ≤ lam + v i := by
    intro i j
    have hi : Finset.univ.sup' Finset.univ_nonempty (fun k => A i k + v k) = lam + v i := h i
    rw [← hi]
    exact Finset.le_sup' (fun k => A i k + v k) (Finset.mem_univ j)
  -- so each step is bounded by `lam` plus a telescoping difference
  have hstep : ∀ t : ℕ, A (c t) (c (t + 1)) ≤ lam + (v (c t) - v (c (t + 1))) := by
    intro t
    have := hle (c t) (c (t + 1))
    linarith
  calc pathWeight A c m = ∑ t ∈ Finset.range m, A (c t) (c (t + 1)) := rfl
    _ ≤ ∑ t ∈ Finset.range m, (lam + (v (c t) - v (c (t + 1)))) :=
        Finset.sum_le_sum fun t _ => hstep t
    _ = (m : ℝ) * lam + ∑ t ∈ Finset.range m, (v (c t) - v (c (t + 1))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (m : ℝ) * lam + (v (c 0) - v (c m)) := by
        rw [Finset.sum_range_sub' (fun t => v (c t)) m]
    _ = (m : ℝ) * lam := by rw [hc]; ring
