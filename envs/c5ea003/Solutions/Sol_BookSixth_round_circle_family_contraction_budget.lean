-- Prove2me | solution 1 for BookSixth.round_circle_family_contraction_budget
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T05:55:31.078198+00:00
-- url     : https://prove2.me/submissions/b7f1376b-5b47-4dee-9ab9-25db6d33e502

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

set_option autoImplicit false

theorem solution : ¬ (∀ {m : ℕ} (c : Fin m → Space3) (R : ℝ) (hR : 0 < R)
    (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    (hsum : ∑ i, (1 - a i) < 1 / 2)
    (chi : Fin m → Space3 → ℝ) (S : Fin m → Space3 → Space3)
    (hchi : ∀ i, Continuous (chi i))
    (hone : ∀ i x, ‖x - c i‖ ≤ R / 2 → chi i x = 1)
    (hzero : ∀ i j x, i ≠ j → ‖x - c j‖ ≥ 5 * R / 2 → chi i x = 0)
    (hS : ∀ i, Continuous (S i))
    (hcen : ∀ i x, S i x - x = (a i - 1) • (x - c i)),
    ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖
        ≤ 2 * (∑ i, (1 - a i)) * ‖x - y‖) := by
  intro hall
  let c : Fin 1 → Space3 := fun _ => 0
  let a : Fin 1 → ℝ := fun _ => 3 / 4
  let S : Fin 1 → Space3 → Space3 := fun _ z => (3 / 4 : ℝ) • z
  let chi : Fin 1 → Space3 → ℝ := fun _ z => 1 + max 0 (‖z‖ - 1)
  have hchi : ∀ i : Fin 1, Continuous (chi i) := by
    intro i
    dsimp [chi]
    fun_prop
  have hone : ∀ (i : Fin 1) (x : Space3), ‖x - c i‖ ≤ (2 : ℝ) / 2 → chi i x = 1 := by
    intro i x hx
    have hx' : ‖x‖ ≤ 1 := by simpa [c] using hx
    simp [chi, max_eq_left (sub_nonpos.mpr hx')]
  have hzero : ∀ (i j : Fin 1) (x : Space3), i ≠ j → ‖x - c j‖ ≥ 5 * (2 : ℝ) / 2 → chi i x = 0 := by
    intro i j x hij _
    exact (hij (Subsingleton.elim i j)).elim
  have hS : ∀ i : Fin 1, Continuous (S i) := by
    intro i
    dsimp [S]
    fun_prop
  have hcen : ∀ (i : Fin 1) (x : Space3), S i x - x = (a i - 1) • (x - c i) := by
    intro i x
    simp only [S, a, c, sub_zero, sub_smul, one_smul]
  have hb := hall c 2 (by norm_num) a (by intro i; norm_num [a])
    (by intro i; norm_num [a]) (by norm_num [a]) chi S hchi hone hzero hS hcen
    (fun _ => (4 : ℝ)) 0
  have hn : ‖(fun _ : Fin 3 => (4 : ℝ))‖ = 4 := by simp
  have hvec : (4 : ℝ) • ((3 / 4 : ℝ) • (fun _ : Fin 3 => (4 : ℝ)) - (fun _ => 4)) =
      (fun _ : Fin 3 => (-4 : ℝ)) := by ext i; norm_num
  norm_num [chi, S, a, hn, hvec] at hb
