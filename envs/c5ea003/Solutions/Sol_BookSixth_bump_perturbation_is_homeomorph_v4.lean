-- Prove2me | solution 1 for BookSixth.bump_perturbation_is_homeomorph_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T01:43:53.116973+00:00
-- url     : https://prove2.me/submissions/0986b113-112a-47ca-9c83-74b8a70e2084

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_small_displacement_is_homeomorph
open scoped BigOperators
open BookSixth

-- # A cut-off perturbation is a homeomorphism under a global small-Lipschitz
--   bound, with no Lipschitz hypothesis on the individual maps
--
-- This is the accepted proof of `BookSixth.bump_perturbation_is_homeomorph_v3`
-- verbatim except that the two `LipschitzWith 1` hypotheses are replaced by
-- continuity.  The Lipschitz constants were never load-bearing: the
-- homeomorphism is produced entirely by `small_displacement_is_homeomorph`
-- applied to the displacement field, whose global bound is `hlipE`.

theorem solution
    (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (hchi : ∀ i, Continuous (chi i))
    (hS : ∀ i, Continuous (S i))
    (hlipE : ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖ ≤ q * ‖x - y‖) :
    ∃ F : Space3 → Space3,
      Continuous F ∧
      ∃ Finv : Space3 → Space3, Continuous Finv ∧
        (∀ x, Finv (F x) = x) ∧ (∀ x, F (Finv x) = x) ∧
        (∀ x, F x = x + ∑ i, chi i x • (S i x - x)) := by
  classical
  -- Each summand is continuous: `chi i` and `S i` are continuous by
  -- hypothesis, and `Continuous.smul` closes the scalar-vector product.
  have hterm : ∀ i, Continuous fun x : Space3 => chi i x • (S i x - x) := by
    intro i
    exact Continuous.smul (hchi i) (Continuous.sub (hS i) continuous_id)
  -- The displacement field is the finite sum of the continuous summands.
  have hEc : Continuous fun x : Space3 => ∑ i, chi i x • (S i x - x) := by
    fun_prop
  -- The total map is the identity plus the displacement field.
  have hS₀c : Continuous fun x : Space3 => x + ∑ i, chi i x • (S i x - x) :=
    Continuous.add continuous_id hEc
  -- The displacement of that map is exactly the field, whose bound is `hlipE`.
  have hS₀lip : ∀ x y : Space3,
      ‖((fun x : Space3 => x + ∑ i, chi i x • (S i x - x)) x - x)
        - ((fun x : Space3 => x + ∑ i, chi i x • (S i x - x)) y - y)‖
        ≤ q * ‖x - y‖ := by
    intro x y
    simp only [add_sub_cancel_left]
    exact hlipE x y
  obtain ⟨Finv, hFic, hli, hri, hbound⟩ :=
    BookSixth.small_displacement_is_homeomorph q ⟨hq, hq1⟩
      (fun x : Space3 => x + ∑ i, chi i x • (S i x - x)) hS₀c hS₀lip
  refine ⟨fun x : Space3 => x + ∑ i, chi i x • (S i x - x), hS₀c, Finv, hFic, hli, hri, ?_⟩
  intro x
  rfl
