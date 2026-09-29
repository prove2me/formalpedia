-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_simple_collinear_has_open_unit_chord
-- name    : ErdosProblems.Erdos1041.PaperCompleteR21.simple_collinear_has_open_unit_chord
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T12:24:48.465216+00:00
-- url     : https://prove2.me/theorems/1b0f1b56-ceeb-4285-9add-d68b6a741272
-- title:
--   A nondegenerate chord inside the open unit sublevel set
-- statement:
--   Let f be a monic complex polynomial of degree n at least 2 whose roots lie on one affine line. Assume every indexed factorization of f along that line has distinct root coordinates, and that the sharp diameter bound C_n(D/2)^n is strictly below 1 for each such factorization and greatest pairwise root distance D. Then f has two distinct zeros a and b, and its absolute value is less than 1 at every point of their closed segment. This is a consequence of the published sharp collinear root-diameter theorem, not a statement of the full historical Erdős #1041 path-length problem.
-- source:
--   Derived from Will Cook, Erdős #1041 paper, Theorem res:sharp-collinear-root-diameter, https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/1041/erdos-1041-lemniscate-newton-flow.tex ; published Lean theorem https://prove2.me/theorems/d6293174-278a-4d7f-b89b-1f95cb82ba37

import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Mathlib
set_option autoImplicit false
open Polynomial Set

theorem ErdosProblems.Erdos1041.PaperCompleteR21.simple_collinear_has_open_unit_chord {n : ℕ} (hn : 2 ≤ n)
    (f : ℂ[X]) (hf : f.IsMonicOfDegree n) (base dir : ℂ)
    (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hindexed : ∀ y : Fin n → ℝ,
      f = (∏ i, (X - C (base + dir * (y i : ℂ)))) →
      Function.Injective (fun i : Fin n => base + dir * (y i : ℂ)))
    (hmargin : ∀ (y : Fin n → ℝ),
      f = (∏ i, (X - C (base + dir * (y i : ℂ)))) →
      ∀ D : ℝ,
        IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) *
          (D / 2) ^ n < 1) :
    ∃ a b : ℂ, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ∀ z ∈ segment ℝ a b, ‖f.eval z‖ < 1 := by sorry
