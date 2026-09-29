-- Prove2me | Theorems.Thm_Langlands_symSatake_prod
-- name    : Langlands.symSatake_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:46:50.153678+00:00
-- url     : https://prove2.me/theorems/d2582248-5ce5-4d4b-b3c0-1441cd77116b
-- title:
--   The product of all `Sym^n` Satake parameters is `(ab)^{n(n+1)/2}`: the central character
-- statement:
--   The product of all `Sym^n` Satake parameters is `(ab)^{n(n+1)/2}`: the central character
--   of the lift is the `n(n+1)/2`-th power of the central character of `Ï`.
--
--   ```lean
--   theorem Langlands.symSatake_prod(n : ℕ) (a b : R) :
--       ∏ i ∈ range (n + 1), symSatake n a b i = (a * b) ^ (∑ i ∈ range (n + 1), i) := by sorry
--
--
--
--   variable {R : Type*} [CommRing R]
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--   variable {R : Type*} [CommRing R]
--
--
--
--
--
--   variable {R : Type*} [CommRing R]
--
--
--
--
--
--
--
--
--
--
--
--
--
--   variable {R : Type*} [CommRing R]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/LanglandsSymmetricPower.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/LanglandsSymmetricPower.lean#L69

-- Thm stub generated from Shared/LanglandsSymmetricPower.lean
import Mathlib
import Definitions.Def_Shared_LanglandsFunctorialityCore
import Definitions.Def_Shared_LanglandsSymmetricPower

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

theorem Langlands.symSatake_prod(n : ℕ) (a b : R) :
    ∏ i ∈ range (n + 1), symSatake n a b i = (a * b) ^ (∑ i ∈ range (n + 1), i) := by sorry
