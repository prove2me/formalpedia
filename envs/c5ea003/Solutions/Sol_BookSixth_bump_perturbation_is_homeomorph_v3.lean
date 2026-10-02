-- Prove2me | solution 1 for BookSixth.bump_perturbation_is_homeomorph_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T20:33:23.208458+00:00
-- url     : https://prove2.me/submissions/e8ee6df4-7185-434a-97f6-87cdf45d1538

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_small_displacement_is_homeomorph

noncomputable section

open scoped BigOperators
open BookSixth

/-- **Corrected finite-sum homeomorphism criterion.**

`BookSixth.bump_perturbation_is_homeomorph_v2` (24b19980) is *Proved* but
applicably unusable for the roundness-preserving ambient motion of Chapter 15:
its hypothesis `n * (2 * L + q) < 1` is combined with `hchiL : ∀ i x, ‖chi i x‖ ≤ L`
and the requirement that `chi i = 1` on a neighbourhood of the component `C i`.
That forces `L ≥ 1` for every `i`, so `hLip` degenerates to `2 < 1` at `n = 1, q = 0`,
which is false for every `n`.

The correct criterion bounds the **Lipschitz constant of the displacement field**
rather than the *size* of the cut-off, and that is exactly what
`BookSixth.small_displacement_is_homeomorph` (5f342cbf) consumes. The analytic
estimate is supplied by the Lipschitz children (`00c3e7a7`, `d456c9e2`), whose
per-summand constant is the crude form of the sharper `c * M + C * L` of
`BookSixth.smul_lipschitz_bound` (d456c9e2).

This child is the bridge that makes the cut-off construction applicable at all. -/
theorem solution
    (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (hchi : ∀ i, LipschitzWith 1 (chi i))
    (hS : ∀ i, LipschitzWith 1 (S i))
    (hlipE : ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖ ≤ q * ‖x - y‖) :
    ∃ F : Space3 → Space3,
      Continuous F ∧
      ∃ Finv : Space3 → Space3, Continuous Finv ∧
        (∀ x, Finv (F x) = x) ∧ (∀ x, F (Finv x) = x) ∧
        (∀ x, F x = x + ∑ i, chi i x • (S i x - x)) := by
  classical
  -- Each summand is continuous: `LipschitzWith` supplies continuity of `chi i`
  -- and `S i`, and `Continuous.smul` closes the scalar-vector product.
  have hchiC : ∀ i, Continuous (chi i) := fun i => (hchi i).continuous
  have hSC : ∀ i, Continuous (S i) := fun i => (hS i).continuous
  have hterm : ∀ i, Continuous fun x : Space3 => chi i x • (S i x - x) := by
    intro i
    exact Continuous.smul (hchiC i) (Continuous.sub (hSC i) continuous_id)
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
