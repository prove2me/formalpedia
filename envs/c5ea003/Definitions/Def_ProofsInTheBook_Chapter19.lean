-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter19
-- name    : ProofsInTheBook_Chapter19
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:57:00.360594+00:00
-- url     : https://prove2.me/theorems/fd3d1f84-dc19-4c26-aba7-4a075ee6bee0
-- title:
--   Translation of a complex polynomial
-- statement:
--   For a complex polynomial $p\in\mathbb C[X]$ and a complex number $z_0$, define the translated polynomial by
--   $$T_{z_0}p=p\circ(X+z_0).$$
--   Thus $(T_{z_0}p)(w)=p(w+z_0)$ for every complex w. Translation is defined for every polynomial, including constant and zero polynomials; no degree condition is part of this definition.
-- source:
--   Mathematical definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter19.lean#L24. Topic: Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 21, “The fundamental theorem of algebra” (https://doi.org/10.1007/978-3-662-57265-8_21). The repository citation specifies the definitions retained here.

import Mathlib.Topology.Algebra.Polynomial
import Mathlib

/-!
# Chapter 19: The fundamental theorem of algebra

From "Proofs from THE BOOK":

**FTA**: Every non-constant polynomial with complex coefficients has a root.

The book presents a proof using the minimum modulus principle:
Consider |p(z)| for a polynomial p of degree n ≥ 1. Since |p(z)| → ∞
as |z| → ∞, the minimum of |p(z)| is attained at some z₀. If |p(z₀)| > 0,
write p(z₀ + w) = p(z₀) + cₘwᵐ + higher terms (m ≥ 1). Choosing w
to make cₘwᵐ point opposite to p(z₀) reduces |p(z₀ + w)| < |p(z₀)|,
contradicting minimality.
-/

namespace ProofsInTheBook.Chapter19

open Polynomial Bornology

/-- Translate a polynomial to local coordinates around `z₀`: `w ↦ p(w + z₀)`. -/
noncomputable def shiftedPolynomial (p : ℂ[X]) (z₀ : ℂ) : ℂ[X] :=
  p.comp (Polynomial.X + Polynomial.C z₀)





























end ProofsInTheBook.Chapter19


