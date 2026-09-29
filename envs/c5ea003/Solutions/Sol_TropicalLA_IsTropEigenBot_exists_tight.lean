-- Prove2me | solution 1 for TropicalLA.IsTropEigenBot.exists_tight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:21:18.18782+00:00
-- url     : https://prove2.me/submissions/2aae8272-b74b-4d89-894a-505def7f8b71

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}
    {v : ι → ℝ} (h : IsTropEigenBot A lam v) (i : ι) :
    ∃ j, A i j ≠ ⊥ ∧ finPart A i j + v j = lam + v i := by
  -- on the support, `finPart` is a section of the coercion
  have hcoe : ∀ {a b : ι}, A a b ≠ ⊥ → ((finPart A a b : ℝ) : WithBot ℝ) = A a b := by
    intro a b hab
    obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hab
    show (((A a b).unbotD 0 : ℝ) : WithBot ℝ) = A a b
    rw [← hr]
    simp
  have hi : Finset.univ.sup (fun j => A i j + (v j : WithBot ℝ))
      = ((lam + v i : ℝ) : WithBot ℝ) := h i
  -- the supremum over a nonempty finset is attained
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
    (fun j => A i j + (v j : WithBot ℝ))
  rw [hj] at hi
  -- the attained value is a genuine real, so the entry cannot be `⊥`
  have hne : A i j ≠ ⊥ := by
    intro hb
    rw [hb, WithBot.bot_add] at hi
    exact WithBot.coe_ne_bot hi.symm
  refine ⟨j, hne, ?_⟩
  rw [← hcoe hne, ← WithBot.coe_add] at hi
  exact WithBot.coe_injective hi
