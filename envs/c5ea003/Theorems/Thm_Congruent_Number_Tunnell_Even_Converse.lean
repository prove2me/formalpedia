-- Prove2me | Theorems.Thm_Congruent_Number_Tunnell_Even_Converse
-- name    : Congruent_Number_Tunnell_Even_Converse
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-06-25T18:46:42.997305+00:00
-- url     : https://prove2.me/theorems/d41622f6-bfa9-4852-b125-2373592276d1
-- statement:
--   **Tunnell's theorem — converse, even case (conditional on BSD).** For squarefree even $n$: if $2\,|C_n| = |D_n|$, where $C_n=\{(x,y,z)\in\mathbb{Z}^3 : n=8x^2+2y^2+64z^2\}$ and $D_n=\{(x,y,z) : n=8x^2+2y^2+16z^2\}$, then $n$ is a congruent number. (Statement following the DeepMind formal-conjectures library.)
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/CongruentNumber.lean

import Mathlib

def congruentNumberDM (n : ℕ) : Prop :=
  ∃ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 ∧ (n : ℚ) = (2⁻¹ : ℚ) * a * b

def C_DM (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | (n : ℤ) = 8 * x ^ 2 + 2 * y ^ 2 + 64 * z ^ 2}
def D_DM (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | (n : ℤ) = 8 * x ^ 2 + 2 * y ^ 2 + 16 * z ^ 2}

theorem Congruent_Number_Tunnell_Even_Converse (n : ℕ) (hsqf : Squarefree n) (heven : Even n) :
    2 * (C_DM n).ncard = (D_DM n).ncard → congruentNumberDM n := by sorry
