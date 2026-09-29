-- Prove2me | solution 1 for TropicalLA.IsTropEigenBot.suppCycle_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T09:24:17.639775+00:00
-- url     : https://prove2.me/submissions/0eaddd23-7a6f-4ac1-bbed-a72449c26f00

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}
    {v : ι → ℝ} (h : IsTropEigenBot A lam v) {m : ℕ} {c : ℕ → ι}
    (hw : IsSuppWalk A c m) (hc : c m = c 0) :
    pathWeight (finPart A) c m ≤ m * lam := by
  -- on the support, `finPart` is a section of the coercion
  have hcoe : ∀ {x y : ι}, A x y ≠ ⊥ → ((finPart A x y : ℝ) : WithBot ℝ) = A x y := by
    intro x y hxy
    obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hxy
    show (((A x y).unbotD 0 : ℝ) : WithBot ℝ) = A x y
    rw [← hr]
    simp
  -- so subinvariance descends to `ℝ` along support edges
  have hle : ∀ i j, A i j ≠ ⊥ → finPart A i j + v j ≤ lam + v i := by
    intro i j hij
    have hi : Finset.univ.sup (fun k => A i k + (v k : WithBot ℝ))
        = ((lam + v i : ℝ) : WithBot ℝ) := h i
    have hb : A i j + (v j : WithBot ℝ) ≤ ((lam + v i : ℝ) : WithBot ℝ) := by
      rw [← hi]
      exact Finset.le_sup (f := fun k => A i k + (v k : WithBot ℝ)) (Finset.mem_univ j)
    rw [← hcoe hij, ← WithBot.coe_add] at hb
    exact_mod_cast hb
  have hstep : ∀ t, t < m → finPart A (c t) (c (t + 1)) ≤ lam + (v (c t) - v (c (t + 1))) := by
    intro t ht
    have := hle (c t) (c (t + 1)) (hw t ht)
    linarith
  calc pathWeight (finPart A) c m = ∑ t ∈ Finset.range m, finPart A (c t) (c (t + 1)) := rfl
    _ ≤ ∑ t ∈ Finset.range m, (lam + (v (c t) - v (c (t + 1)))) :=
        Finset.sum_le_sum fun t ht => hstep t (Finset.mem_range.mp ht)
    _ = (m : ℝ) * lam + ∑ t ∈ Finset.range m, (v (c t) - v (c (t + 1))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (m : ℝ) * lam + (v (c 0) - v (c m)) := by
        rw [Finset.sum_range_sub' (fun t => v (c t)) m]
    _ = (m : ℝ) * lam := by rw [hc]; ring
