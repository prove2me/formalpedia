-- Prove2me | solution 1 for TropicalLA.IsTropEigen.iterate_injOn_of_minimal_period
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:50:15.358653+00:00
-- url     : https://prove2.me/submissions/e8746517-7eec-42bf-9a5a-61486ac0f60f

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
theorem solution {ι : Type*} {f : ι → ι} {y : ι} {p : ℕ}
    (hp : f^[p] y = y) (hmin : ∀ q, 0 < q → q < p → f^[q] y ≠ y) :
    Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) := by
  -- if `f^[a] y = f^[b] y` with `a < b < p`, then applying `f^[p - a]` gives `f^[b - a] y = y`
  have key : ∀ a b, a < b → b < p → f^[a] y = f^[b] y → False := by
    intro a b hab hbp h
    apply hmin (b - a) (by omega) (by omega)
    have h' := congrArg (f^[p - a]) h
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show p - a + a = p by omega, hp, show p - a + b = (b - a) + p by omega,
      Function.iterate_add_apply, hp] at h'
    exact h'.symm
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h hb hab
  · exact key b a h ha hab.symm
