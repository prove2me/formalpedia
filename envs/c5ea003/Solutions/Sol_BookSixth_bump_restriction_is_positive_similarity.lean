-- Prove2me | solution 1 for BookSixth.bump_restriction_is_positive_similarity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T06:50:09.450651+00:00
-- url     : https://prove2.me/submissions/d452eb78-7bf8-4ec0-aee2-0643c5a49587

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_patch_agrees_with_its_own_similarity

noncomputable section

open scoped BigOperators
open BookSixth

/-- **The cut-off patched motion agrees with each component's own similarity.**

The patched map `x + ∑ j, chi j x • (S j x - x)` collapses, at a point `x` of
the component `C i`, to the local similarity `S i x` that moves that component.
This is the hinge between the cut-off construction and the roundness lemma. -/
theorem solution {n : ℕ}
    (C : Fin n → Set Space3) (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (A : Fin n → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (a : Fin n → ℝ) (b : Fin n → Fin 3 → ℝ)
    (hone : ∀ i x, x ∈ C i → chi i x = 1)
    (hzero : ∀ i j x, i ≠ j → x ∈ C i → chi j x = 0)
    (hS : ∀ i x, S i x = a i • (A i x) + b i) :
    ∀ (i : Fin n) (x : Space3), x ∈ C i →
      x + ∑ j, chi j x • (S j x - x) = a i • (A i x) + b i := by
  intro i x hx
  -- At `x ∈ C i` the own cut-off is one and every other cut-off vanishes.
  have hone' : chi i x = 1 := hone i x hx
  have hzero' : ∀ j ∈ Finset.univ, j ≠ i → chi j x = 0 := by
    intro j _ hji
    exact hzero i j x (Ne.symm hji) hx
  -- The sum collapses to the own similarity, which is the translate/rotate/scale form.
  calc x + ∑ j, chi j x • (S j x - x)
      = S i x := patch_agrees_with_its_own_similarity i chi S x hone' hzero'
    _ = a i • (A i x) + b i := hS i x

end
