-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_residue_window_hit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:09:18.963519+00:00
-- url     : https://prove2.me/submissions/05a00cc9-7ccd-4fe9-aa98-258950ebec18

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_three_window_hit
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# From actual modular cubic roots to the exceptional-set density

Rational profile coefficients are cleared over the
integers before reduction. There is deliberately no ring homomorphism from
`ℚ` to `ZMod p`. The final theorem is conditional on an actual divergent family
of good primes; producing that family from a number-field nonsquare remains a
separate global obligation, not a premise silently claimed to have been proved.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open scoped BigOperators
end ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℤ) (P : ℕ → ℚ) (q A B : ℤ) (T n : ℕ) (hn : T ≤ n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (p : ℕ) [Fact p.Prime] (r : ZMod p)
    (hroot : (A : ZMod p) * (r ^ 3 - r) + (B : ZMod p) = 0)
    (hfactor : 3 * (A : ZMod p) * r ≠ 0)
    (hns : ¬ IsSquare (r ^ 2 - 1)) (hphase : (n : ZMod p) = r - 2) :
    ∃ j : ℕ, j < 3 ∧ (u (n + j) : ℚ) ≠ P (n + j) := by
  let U : ℕ → ZMod p := fun k ↦ (q : ZMod p) * (u k : ZMod p)
  let V : ℕ → ZMod p := fun k ↦ (q : ZMod p) * (v k : ZMod p)
  let b : ℕ → ZMod p := fun k ↦ (a k : ZMod p)
  have hU : ∀ j, T ≤ j → U (j + 1) = b j * U j - V j := by
    intro j hj
    have h : (u (j + 1) : ZMod p) + (v j : ZMod p) =
        (a j : ZMod p) * (u j : ZMod p) := by
      simpa using congrArg (Int.castRingHom (ZMod p)) (hnum j hj)
    dsimp [U, V, b]
    linear_combination (q : ZMod p) * h
  have hV : ∀ j, T ≤ j → V (j + 1) = b j * V j := by
    intro j hj
    have h : (v (j + 1) : ZMod p) = (a j : ZMod p) * (v j : ZMod p) := by
      simpa using congrArg (Int.castRingHom (ZMod p)) (hden j hj)
    dsimp [V, b]
    rw [h]
    ring
  obtain ⟨j, hj, hne⟩ := cubic_three_window_hit U V b (A : ZMod p) (B : ZMod p)
    r T n hn hU hV hroot hfactor hns hphase
  refine ⟨j, hj, ?_⟩
  intro hagree
  apply hne
  have hQ : (q : ℚ) * (u (n + j) : ℚ) =
      (A : ℚ) * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
        (((n + j : ℕ) : ℚ) + 2) + (B : ℚ) := by
    rw [hagree]
    exact hclear (n + j)
  have hZ : q * u (n + j) = A * ((n + j : ℕ) : ℤ) *
      (((n + j : ℕ) : ℤ) + 1) * (((n + j : ℕ) : ℤ) + 2) + B := by
    exact_mod_cast hQ
  have hF : (q : ZMod p) * (u (n + j) : ZMod p) =
      (A : ZMod p) * ((n + j : ℕ) : ZMod p) * (((n + j : ℕ) : ZMod p) + 1) *
        (((n + j : ℕ) : ZMod p) + 2) + (B : ZMod p) := by
    simpa using congrArg (Int.castRingHom (ZMod p)) hZ
  dsimp [U]
  rw [hF]
  ring
