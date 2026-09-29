-- Prove2me | solution 1 for TropicalLA.IsTropEigen.exists_critical_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:34:22.258894+00:00
-- url     : https://prove2.me/submissions/c232c0dd-35bc-48e4-b8fd-b412dc443d97

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}
    (h : IsTropEigen A lam v) :
    ∃ (f : ι → ι) (y : ι) (p : ℕ), 0 < p ∧ f^[p] y = y ∧
      Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) ∧
      (∀ i, A i (f i) + v (f i) = lam + v i) ∧
      pathWeight A (fun t => f^[t] y) p = p * lam := by
  -- a tight successor map with a point of minimal period
  obtain ⟨f, y, p, hp, hfp, hmin, htight⟩ := h.exists_minimal_periodic_point
  refine ⟨f, y, p, hp, hfp, ?_, htight, ?_⟩
  · -- minimal period ⇒ the first `p` orbit points are distinct
    have key : ∀ a b, a < b → b < p → f^[a] y = f^[b] y → False := by
      intro a b hab hbp hfab
      apply hmin (b - a) (by omega) (by omega)
      have h' := congrArg (f^[p - a]) hfab
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show p - a + a = p by omega, hfp, show p - a + b = (b - a) + p by omega,
        Function.iterate_add_apply, hfp] at h'
      exact h'.symm
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact key a b hlt hb hab
    · exact key b a hgt ha hab.symm
  · -- along tight steps the weight telescopes: `mλ + v y - v (f^m y)`
    have htel : ∀ m, pathWeight A (fun t => f^[t] y) m = m * lam + v y - v (f^[m] y) := by
      intro m
      induction m with
      | zero => simp [pathWeight]
      | succ m ih =>
        have hw : pathWeight A (fun t => f^[t] y) (m + 1)
            = pathWeight A (fun t => f^[t] y) m + A (f^[m] y) (f^[m + 1] y) := by
          simp only [pathWeight, Finset.sum_range_succ]
        rw [hw, ih, Function.iterate_succ_apply']
        have := htight (f^[m] y)
        push_cast
        linarith
    rw [htel, hfp]
    ring
