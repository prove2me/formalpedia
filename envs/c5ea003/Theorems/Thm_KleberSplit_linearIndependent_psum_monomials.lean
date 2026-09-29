-- Prove2me | Theorems.Thm_KleberSplit_linearIndependent_psum_monomials
-- name    : KleberSplit.linearIndependent_psum_monomials
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:44:09.949897+00:00
-- url     : https://prove2.me/theorems/d1d348b1-2994-4dc5-b67c-155479dc743f
-- title:
--   Linear independence of power-sum monomials.
-- statement:
--   **Linear independence of power-sum monomials.**
--
--   A family of products of power sums `∏_{j ∈ s} p_{k_i j}` (all exponents positive, at least
--   `s.card` variables available) is linearly independent as soon as the multisets of exponents
--   `{k_i j : j ∈ s}` are pairwise distinct.  This is a corollary of the many-fold independence
--   theorem, obtained from `m_{(k)} = p_k`.
--
--   ```lean
--   theorem KleberSplit.linearIndependent_psum_monomials{M : ℕ} [IsDomain R] [CharZero R]
--       {ι κ : Type*} [Fintype ι] [DecidableEq κ] (s : Finset κ) (k : ι → κ → ℕ)
--       (hk : ∀ i, ∀ j ∈ s, k i j ≠ 0) (hcard : s.card ≤ M + 1)
--       (hinj : Function.Injective fun i => (s.val.map (k i) : Multiset ℕ)) :
--       LinearIndependent R (fun i => ∏ j ∈ s, psum R (M + 1) (k i j)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KleberManyFoldProducts.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KleberManyFoldProducts.lean#L349

-- Thm stub generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
/-
# Many-fold complementary products of monomial symmetric functions

A continuation of `Algebra.KleberComplementaryProducts`.  The quadratic-statistic
triangularity used there for products of *two* monomial symmetric functions is not tied to
two factors: here we prove that products `m_{α_1} ⋯ m_{α_r}` of arbitrarily many monomial
symmetric functions are linearly independent as soon as the multiset unions
`parts α_1 + ⋯ + parts α_r` are pairwise distinct.

## Main results

* `KleberSplit.linearIndependent_msym_prod` — many-fold independence.
* `KleberSplit.linearIndependent_psum_monomials` — corollary: linear independence of
  power-sum monomials `p_{k_1} ⋯ p_{k_r}` indexed by multisets of positive exponents.
-/


open KleberSplit

open Finsupp MvPolynomial Finset

variable {N : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]

/-! ### Products of arbitrarily many factors

The mechanism above is not restricted to *two* factors.  We now prove the sharper
statement: products `m_{α_1} ⋯ m_{α_r}` of arbitrarily many monomial symmetric functions
are linearly independent as soon as the multiset unions `parts α_1 + ⋯ + parts α_r` are
pairwise distinct.  For `r = 2` this recovers the theorem above.
-/







/-! #### Coefficients of many-fold products -/






/-! ### Application: linear independence of power-sum monomials

Since `m_{(k)} = p_k` is the power sum, a product `∏_j p_{k_j}` is a monomial in the power
sums, and its multiset union is exactly the multiset `{k_j}` of exponents.  The many-fold
theorem therefore recovers the linear independence of the power-sum monomials
`p_{k_1} ⋯ p_{k_r}` indexed by multisets of positive integers, provided there are at least
as many variables as factors.
-/

theorem KleberSplit.linearIndependent_psum_monomials{M : ℕ} [IsDomain R] [CharZero R]
    {ι κ : Type*} [Fintype ι] [DecidableEq κ] (s : Finset κ) (k : ι → κ → ℕ)
    (hk : ∀ i, ∀ j ∈ s, k i j ≠ 0) (hcard : s.card ≤ M + 1)
    (hinj : Function.Injective fun i => (s.val.map (k i) : Multiset ℕ)) :
    LinearIndependent R (fun i => ∏ j ∈ s, psum R (M + 1) (k i j)) := by sorry
