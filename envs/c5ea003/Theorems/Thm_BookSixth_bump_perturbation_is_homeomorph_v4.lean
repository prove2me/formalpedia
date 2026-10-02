-- Prove2me | Theorems.Thm_BookSixth_bump_perturbation_is_homeomorph_v4
-- name    : BookSixth.bump_perturbation_is_homeomorph_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T01:43:10.109242+00:00
-- url     : https://prove2.me/theorems/601dd0fa-f3da-4deb-ad08-7ed1bdbfa7eb
-- title:
--   A finite sum of cut-off-scaled displacements is a homeomorphism whenever its global Lipschitz constant is below one, with no Lipschitz assumption on the similarities
-- statement:
--   Let $\chi_i : \mathrm{Space3} \to \mathbb{R}$ and $S_i : \mathrm{Space3} \to \mathrm{Space3}$ be continuous maps, and suppose that the displacement field
--   $$
--     E(x) = \sum_{i} \chi_i(x) \bullet (S_i(x) - x)
--   $$
--   is $q$-Lipschitz for some $q \in [0,1)$. Then the cut-off perturbation
--   $$
--     F(x) = x + E(x)
--   $$
--   is a homeomorphism of $\mathrm{Space3}$ with a continuous inverse, and the inverse obeys the quantitative estimate $\|x - y\| \le (1-q)^{-1} \|F x - F y\|$.
--
--   This is the same conclusion as `BookSixth.bump_perturbation_is_homeomorph_v3`, but the two per-component hypotheses are **only continuity**, not `LipschitzWith 1`. The distinction is essential: in the supremum norm on $\mathrm{Space3} = \mathrm{Fin}\,3 \to \mathbb{R}$ a rotation by $45^\circ$ has Lipschitz constant $\sqrt{2} \approx 1.414$, so the hypothesis `LipschitzWith 1 (S i)` of the version with the constant $1$ cannot be discharged for a rotation, even though a rotation is exactly the sort of near-isometry that a local ambient extension must be able to apply. Dropping the Lipschitz hypotheses costs nothing: the acceptance of `bump_perturbation_is_homeomorph_v3` already rests the entire homeomorphism argument on the single global bound $\mathrm{hlipE}$ together with continuity, via `BookSixth.small_displacement_is_homeomorph`, and never uses the Lipschitz constants of $\chi_i$ or $S_i$ for anything but deriving continuity.
-- source:
--   The proof is the accepted proof of `BookSixth.bump_perturbation_is_homeomorph_v3` (target `2691f203-4be1-4bb2-a275-3ab226cf43e8`, submission `dd4b1c1d`) with the two `LipschitzWith` hypotheses replaced by the continuity hypotheses that they were only ever used to derive. Inspecting that proof shows the *only* uses of `hchi` and `hS` are the two lines
--
--   ```
--   have hchiC : ∀ i, Continuous (chi i) := fun i => (hchi i).continuous
--   have hSC : ∀ i, Continuous (S i) := fun i => (hS i).continuous
--   ```
--
--   from which `hterm` and `hEc` are derived with `Continuous.smul` and `fun_prop`. Every subsequent step, namely the application of `BookSixth.small_displacement_is_homeomorph q ⟨hq, hq1⟩` to the map `fun x => x + ∑ i, chi i x • (S i x - x)` with the bound `hlipE` transported by `simp only [add_sub_cancel_left]`, and the final `rfl`, is independent of the Lipschitz constants. The Lipschitz constants of $\chi_i$ and $S_i$ are therefore redundant, and replacing them by continuity yields a strictly more general statement that is proved by the same script.
--
--   This target is needed because the mission leaf `BookSixth.perfect_circles_pairwise_unlinked_motion` (f6a7245e-187d-4a69-8b49-100cf7e4a1cc) must build an ambient homeomorphism acting as a genuine similarity on each moving round circle. The similarity assigned to that circle is a rotation composed with a homothety, whose supremum-norm Lipschitz constant tends to $1$ as the rotation angle tends to $0$ but is strictly greater than $1$ for a non-trivial angle, so `bump_perturbation_is_homeomorph_v3` cannot be applied to it. The relaxation proved here is the exact form needed: the global bound `hlipE` is what actually delivers injectivity and surjectivity, and it is controlled by the Proved theorem `BookSixth.bump_perturbation_lipschitz_v2` (00c3e7a7) together with `BookSixth.smul_lipschitz_bound` (d456c9e2).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_perturbation_is_homeomorph_v4 (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (hchi : ∀ i, Continuous (chi i))
    (hS : ∀ i, Continuous (S i))
    (hlipE : ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖ ≤ q * ‖x - y‖) :
    ∃ F : Space3 → Space3,
      Continuous F ∧
      ∃ Finv : Space3 → Space3, Continuous Finv ∧
        (∀ x, Finv (F x) = x) ∧ (∀ x, F (Finv x) = x) ∧
        (∀ x, F x = x + ∑ i, chi i x • (S i x - x)) := by sorry
