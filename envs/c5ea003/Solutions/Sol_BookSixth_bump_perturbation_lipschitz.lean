-- Prove2me | solution 1 for BookSixth.bump_perturbation_lipschitz
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T06:02:49.690378+00:00
-- url     : https://prove2.me/submissions/860614d3-3df1-4915-9409-c062bc8409ec

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth
set_option autoImplicit false

theorem solution : ¬ (∀ (n : ℕ) (L M : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (hchi : ∀ i, LipschitzWith 1 (chi i))
    (hchiL : ∀ i x, ‖chi i x‖ ≤ L)
    (hS : ∀ i, LipschitzWith 1 (S i))
    (hSiy : ∀ i y, ‖S i y - y‖ ≤ M),
    ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖ ≤
        (∑ i : Fin n, (L + M)) * ‖x - y‖) := by
  intro hall
  let g : ℝ → ℝ := fun x => max (x - 1 / 2) (min x (-x))
  have hleft : LipschitzWith 1 (fun x : ℝ => x - 1 / 2) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp
  have hneg : LipschitzWith 1 (fun x : ℝ => -x) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp
  have hg : LipschitzWith 1 g := by
    simpa only [g, max_self] using hleft.max (LipschitzWith.id.min hneg)
  have hdis (x : ℝ) : |g x - x| ≤ 1 / 2 := by
    have hlo : x - 1 / 2 ≤ g x := le_max_left _ _
    have hhi : g x ≤ x := max_le (by linarith) (min_le_left _ _)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let S : Fin 1 → Space3 → Space3 := fun _ x i => g (x i)
  have hS : ∀ i : Fin 1, LipschitzWith 1 (S i) := by
    intro i
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    calc
      dist (S i x j) (S i y j) ≤ dist (x j) (y j) := by
        simpa only [S, NNReal.coe_one, one_mul] using hg.dist_le_mul (x j) (y j)
      _ ≤ dist x y := dist_le_pi_dist x y j
  have hbound : ∀ (i : Fin 1) (y : Space3), ‖S i y - y‖ ≤ 1 / 2 := by
    intro i y
    apply (pi_norm_le_iff_of_nonempty (S i y - y)).mpr
    intro j
    simpa only [S, Pi.sub_apply, Real.norm_eq_abs] using hdis (y j)
  have hb := hall 1 1 (1 / 2) (by norm_num) (by norm_num)
    (fun _ _ => 1) S (by intro i; apply lipschitzWith_iff_dist_le_mul.mpr; intro x y; simp)
    (by intro i x; simp) hS hbound (fun _ => (1 / 4 : ℝ)) 0
  norm_num [S, g, Pi.sub_def] at hb

