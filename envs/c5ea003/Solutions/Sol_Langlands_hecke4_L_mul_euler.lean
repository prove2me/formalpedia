-- Prove2me | solution 1 for Langlands.hecke4_L_mul_euler
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:43:37.28892+00:00
-- url     : https://prove2.me/submissions/d26a380d-d590-4ed1-b80b-c3e2f89b24e6

-- Sol generated from Shared/LanglandsSymmetricPower.lean
import Mathlib
import Definitions.Def_Shared_LanglandsFunctorialityCore
import Definitions.Def_Shared_LanglandsSymmetricPower
import Theorems.Thm_Langlands_mk_mul_quartic

/-!
# Langlands functoriality, II: symmetric power liftings and the GL(2) → GL(3) transfer

Building on `Shared.LanglandsFunctorialityCore`, this file constructs the symmetric power
liftings of an unramified `GL(2)` representation at the level of Satake parameters and local
L-functions, and proves the defining properties of the transfers

* `Sym^1` : the identity transfer `GL(2) → GL(2)`;
* `Sym^2` : the **Gelbart–Jacquet lift** `GL(2) → GL(3)`;
* `Sym^3` : the symmetric cube lift `GL(2) → GL(4)`.

The main results are:

* `symL_mul_symEuler` — the Sym^n L-factor inverts the degree `n+1` Euler polynomial;
* `symEuler_two_eq`, `gelbart_jacquet` — the GL(3) Euler factor of `Sym^2 π` has coefficients
  that are *polynomials in the GL(2) Hecke eigenvalues*: `b_p = a_p^2 - χ(p)`,
  `b_{p^2}`-coefficient `= χ(p) b_p`, `det = χ(p)^3`; consequently the Dirichlet coefficients
  of `L(s, Sym^2 π)` satisfy the GL(3) three-term recursion, which is the local statement of
  the Gelbart–Jacquet functorial transfer;
* `symEuler_three_eq`, `symcube_transfer` — the same for the symmetric cube on `GL(4)`;
* `rankin_selberg_sym_two` — the local Rankin–Selberg identity
  `∑_k a_{p^k}^2 X^k · L(Sym^2, X)^{-1} = 1 + χ(p) X`, i.e.
  `L(s, π × π) = ζ_p(s, χ) · L(s, Sym^2 π)` after removing the `ζ`-factor;
* `symL_coeff_one` — the transferred `p`-th Hecke eigenvalue of `Sym^n π` is `h_n(a, b)`;
* `sym_tempered` — temperedness is preserved by every symmetric power lift;
* `symSatake_selfdual`, `symEuler_two_selfdual` — self-duality of the lifts of a
  representation with trivial central character.
-/

open Langlands

open Finset PowerSeries


variable {R : Type*} [CommRing R]











variable {R : Type*} [CommRing R]















variable {R : Type*} [CommRing R]





variable {R : Type*} [CommRing R]



lemma hecke4_add_four (c1 c2 c3 c4 : R) (k : ℕ) :
    hecke4 c1 c2 c3 c4 (k + 4) = c1 * hecke4 c1 c2 c3 c4 (k + 3) - c2 * hecke4 c1 c2 c3 c4 (k + 2)
      + c3 * hecke4 c1 c2 c3 c4 (k + 1) - c4 * hecke4 c1 c2 c3 c4 k := rfl










variable {R : Type*} [CommRing R]













open Langlands in
theorem solution(c1 c2 c3 c4 : R) :
    PowerSeries.mk (hecke4 c1 c2 c3 c4) * gl4Euler c1 c2 c3 c4 = 1 := by
  rw [gl4Euler, mk_mul_quartic _ c1 c2 c3 c4 (fun k => hecke4_add_four c1 c2 c3 c4 k)]
  show (C ((hecke4 c1 c2 c3 c4) 0) * X ^ 0 + C ((hecke4 c1 c2 c3 c4) 1 - c1 * (hecke4 c1 c2 c3 c4) 0) * X ^ 1
      + C ((hecke4 c1 c2 c3 c4) 2 - c1 * (hecke4 c1 c2 c3 c4) 1 + c2 * (hecke4 c1 c2 c3 c4) 0) * X ^ 2
      + C ((hecke4 c1 c2 c3 c4) 3 - c1 * (hecke4 c1 c2 c3 c4) 2 + c2 * (hecke4 c1 c2 c3 c4) 1
          - c3 * (hecke4 c1 c2 c3 c4) 0) * X ^ 3) = 1
  have e0 : (hecke4 c1 c2 c3 c4) 0 = 1 := rfl
  have e1 : (hecke4 c1 c2 c3 c4) 1 = c1 := rfl
  have e2 : (hecke4 c1 c2 c3 c4) 2 = c1 ^ 2 - c2 := rfl
  have e3 : (hecke4 c1 c2 c3 c4) 3 = c1 ^ 3 - 2 * c1 * c2 + c3 := rfl
  rw [e0, e1, e2, e3]
  have z1 : (c1 : R) - c1 * 1 = 0 := by ring
  have z2 : (c1 : R) ^ 2 - c2 - c1 * c1 + c2 * 1 = 0 := by ring
  have z3 : (c1 : R) ^ 3 - 2 * c1 * c2 + c3 - c1 * (c1 ^ 2 - c2) + c2 * c1 - c3 * 1 = 0 := by ring
  rw [z1, z2, z3]
  simp
