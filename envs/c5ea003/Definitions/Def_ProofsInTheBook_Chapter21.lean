-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter21
-- name    : ProofsInTheBook_Chapter21
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T15:12:05.869037+00:00
-- url     : https://prove2.me/theorems/84d71dbb-9ac7-4e4b-898c-2eb812043c2d
-- title:
--   Binomial polynomials and integer-valued rational polynomials
-- statement:
--   For $k\in\mathbb N$, define the rational polynomial $\binom Xk=X(X-1)\cdots(X-k+1)/k!$, with $\binom X0=1$. A rational polynomial is integer-valued when its evaluation at every integer is integral. The bundle defines forward differences, finite Newton expansions, selected integer values, and their integral finite-difference coefficients.
-- source:
--   Existing Lean formalization associated with Aigner and Ziegler, Proofs from THE BOOK. Repository chapter 21; repository numbering is not an edition-specific book chapter number. Exact source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter21.lean

import Mathlib

/-!
# Chapter 21: A theorem of Pólya on polynomials

From "Proofs from THE BOOK":

**Pólya's theorem**: If f(x) is a polynomial with integer values at
all integers, then f can be written as a linear combination of
binomial coefficients C(x,0), C(x,1), C(x,2), ....

The book proves this via finite differences: Δⁿf(0) = ∑(-1)^k C(n,k)f(n-k).
-/

namespace ProofsInTheBook.Chapter21

noncomputable section

open Finset Function Polynomial

/-!
### The finite-difference step

Pólya's theorem is proved by repeatedly applying the forward difference
operator.  The binomial-coefficient basis is adapted to this operator because
`Δ C(x, k + 1) = C(x, k)`, which is just Pascal's identity in polynomial form.
-/









/-!
### Pólya's integer-valued polynomial theorem

We formalize the book theorem for polynomials over `ℚ`: if such a polynomial
takes integer values at every integer, then it is a finite `ℤ`-linear
combination of the binomial polynomials `x ↦ Ring.choose x k`.
-/

/-- The binomial polynomial `x choose k`, represented in `ℚ[X]`. -/
def binomialPolynomial (k : ℕ) : ℚ[X] :=
  (k.factorial : ℚ)⁻¹ • descPochhammer ℚ k







/-- Forward difference on polynomials, `P(x+1)-P(x)`. -/
def polynomialForwardDifference (P : ℚ[X]) : ℚ[X] :=
  P.comp (Polynomial.X + 1) - P

/-- Linear-map packaging of polynomial forward difference. -/
def polynomialForwardDifferenceₗ : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := polynomialForwardDifference
  map_add' P Q := by
    simp [polynomialForwardDifference, add_comp]
    abel
  map_smul' a P := by
    simp [polynomialForwardDifference, Polynomial.smul_comp, smul_sub]









/-- The Newton expansion with rational forward-difference coefficients. -/
def newtonPolynomial (P : ℚ[X]) (n : ℕ) : ℚ[X] :=
  ∑ k ∈ range n, (((fwdDiff (1 : ℚ))^[k] P.eval) 0) • binomialPolynomial k









/-- A rational polynomial is integer-valued if it maps every integer to an integer. -/
def IsIntegerValuedPolynomial (P : ℚ[X]) : Prop :=
  ∀ z : ℤ, ∃ m : ℤ, P.eval (z : ℚ) = (m : ℚ)

def integerValue (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) (z : ℤ) : ℤ :=
  Classical.choose (hP z)



/-- The integer coefficient `Δ^k P(0)`, computed from integer values of `P`. -/
def polyaCoeff (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) (k : ℕ) : ℤ :=
  ∑ i ∈ range (k + 1),
    ((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ)) * integerValue P hP (i : ℤ)





end

end ProofsInTheBook.Chapter21


