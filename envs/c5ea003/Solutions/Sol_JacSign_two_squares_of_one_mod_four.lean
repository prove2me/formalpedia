-- Prove2me | solution 1 for JacSign.two_squares_of_one_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:30.45158+00:00
-- url     : https://prove2.me/submissions/ba87ee29-0007-4f0c-9066-703abd7663b6

-- Sol generated from Tropical/JacobiSignedTwoSquares.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_W_eq_A_one
import Theorems.Thm_JacSign_W_even
import Theorems.Thm_JacSign_chi_neg_one_eq_one
import Theorems.Thm_JacSign_jacobsthal_identity
import Theorems.Thm_JacSign_sum_even_of_neg_invariant

/-!
# The Weil floor is a two-squares identity

The Weil bound `W p ^ 2 ≤ 4 p` of `JacobiSignedWeilFloorBound.lean` is not an accident of
estimation: it is the shadow of an **exact identity**.  Write `A p d = ∑_x χ(x³ - d x)` for
the twisted character sums, and let `ν` be any quadratic nonresidue mod `p`.  For
`p ≡ 1 (mod 4)` we prove

`A p 1 ^ 2 + A p ν ^ 2 = 4 p`   (`JacSign.jacobsthal_identity`)

so the Jacobi-signed circle count `W p = A p 1` and its nonresidue twin `A p ν` are the two
legs of a right triangle with hypotenuse `2 √p`.  Consequences:

* `JacSign.W_sq_add_twist_sq` : the identity phrased for the statistic `W p` itself;
* `JacSign.weil_floor_of_identity` : the Weil bound, re-derived as a corollary;
* `JacSign.two_squares_of_one_mod_four` : **Fermat's two-square theorem** with explicit
  witnesses `p = (W p / 2)² + (A p ν / 2)²` — the signal and its twin are *exactly* the
  Gaussian-integer coordinates of `p`.

Structurally this explains the experimental data: `W p` is `2a` where `p = a² + b²`, hence
its erratic, "unstructured" behaviour, and hence also its inability to leak the factors of
a semiprime — the two legs trade off against each other with `4p` conserved.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]



/-- Every twisted sum is even when `p ≡ 1 (mod 4)`. -/
theorem A_even (hp : p ≠ 2) (h1 : p % 4 = 1) (d : ZMod p) : (2 : ℤ) ∣ A p d := by
  refine sum_even_of_neg_invariant p hp (fun x => quadraticChar (ZMod p) (x ^ 3 - d * x))
    (fun x => ?_) (by simp)
  show quadraticChar (ZMod p) ((-x) ^ 3 - d * (-x)) = quadraticChar (ZMod p) (x ^ 3 - d * x)
  have hx : quadraticChar (ZMod p) ((-x) ^ 3 - d * (-x))
      = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (x ^ 3 - d * x) := by
    rw [← map_mul]; congr 1; ring
  rw [hx, chi_neg_one_eq_one p h1, one_mul]


/-- The identity in terms of the Jacobi-signed circle count itself. -/
theorem W_sq_add_twist_sq (hp : p ≠ 2) (h1 : p % 4 = 1) {v : ZMod p}
    (hv : quadraticChar (ZMod p) v = -1) : (W p) ^ 2 + (A p v) ^ 2 = 4 * (p : ℤ) := by
  rw [W_eq_A_one p h1]
  exact jacobsthal_identity p hp h1 hv




open JacSign in
theorem solution(hp : p ≠ 2) (h1 : p % 4 = 1) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2 ∧ 2 * a = W p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  obtain ⟨v, hv⟩ := quadraticChar_exists_neg_one hF
  obtain ⟨a, ha⟩ : (2 : ℤ) ∣ W p := W_even p hp
  obtain ⟨b, hb⟩ : (2 : ℤ) ∣ A p v := A_even p hp h1 v
  refine ⟨a, b, ?_, by omega⟩
  have h := W_sq_add_twist_sq p hp h1 hv
  rw [ha, hb] at h
  nlinarith [h]
