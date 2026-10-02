-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter27
-- name    : ProofsInTheBook_Chapter27
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:57:13.330445+00:00
-- url     : https://prove2.me/theorems/1332f503-9a0a-4033-ac0f-32c4457c13e2
-- title:
--   Integer-grid rectangle tilings by equal-length bars
-- statement:
--   For natural numbers $n,a,b$, the rectangle is the finite grid $\operatorname{Fin}(a)\times\operatorname{Fin}(b)$. A tiling is a finite family of pairwise disjoint cell sets whose union is the grid. Each member is a horizontal run of $n$ consecutive cells in one row or a vertical run of $n$ consecutive cells in one column, entirely inside the rectangle. Thus the permitted nondegenerate tile shapes are $1\times n$ and $n\times1$.
--
--   The parameterized predicate `IsTiledByNxOne` expresses existence of such a family. The bundle also defines $\omega_n=\exp(2\pi i/n)$; for $n>0$ this is the usual primitive $n$th root of unity. Natural parameters are unrestricted in the definitions, so empty rectangles and zero-length runs follow the literal finite-set conventions.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 29, “Tiling rectangles”, pp. 207–211 (https://doi.org/10.1007/978-3-662-57265-8_29). Original definition source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter27.lean#L81. The generated bundle retains definitions and supporting declarations from this source; the book citation identifies their topic rather than asserting that each auxiliary structure appears in the book.

import Mathlib

/-!
# Chapter 27: Tiling rectangles

From "Proofs from THE BOOK":

**De Bruijn's theorem**: An a × b rectangle can be tiled by 1 × n
rectangles iff n divides a or n divides b.

*Book proof (necessity).* Let ω = e^{2πi/n} (primitive n-th root of unity).
Assign weight ω^{i+j} to cell (i, j). Any 1×n horizontal brick in row r
starting at column c has weight ω^{r+c}(1+ω+...+ω^{n-1}) = 0.  Any n×1
vertical brick in column c starting at row r has weight the same = 0.
So the total weight of the whole tiling is 0.  But the total also factors as
(∑_{i<a} ω^i)(∑_{j<b} ω^j).  Since ℂ is an integral domain, one factor is 0,
so n|a or n|b.
-/

namespace ProofsInTheBook.Chapter27

open Complex Finset Real IsPrimitiveRoot

/-! ### The coloring argument -/

/-- The primitive n-th root of unity ω = e^{2πi/n}. -/
noncomputable def ω (n : ℕ) : ℂ := Complex.exp (2 * π * I / n)











/-! ### The tiling model -/

/--
A partition of Fin a × Fin b into bricks where each brick is either:
- a horizontal run: {(r, c), (r, c+1), ..., (r, c+n-1)} for some row r and column c with c+n ≤ b
- a vertical run:  {(r, c), (r+1, c), ..., (r+n-1, c)} for some col c and row r with r+n ≤ a
-/
def IsTiledByNxOne (n a b : ℕ) : Prop :=
  ∃ (bricks : Finset (Finset (Fin a × Fin b))),
    bricks.biUnion id = Finset.univ ∧
    (∀ B₁ ∈ bricks, ∀ B₂ ∈ bricks, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
    ∀ B ∈ bricks,
      (∃ r : Fin a, ∃ c : ℕ, c + n ≤ b ∧
        B = Finset.univ.filter (fun p : Fin a × Fin b =>
          p.1 = r ∧ c ≤ p.2.val ∧ p.2.val < c + n)) ∨
      (∃ col : Fin b, ∃ r : ℕ, r + n ≤ a ∧
        B = Finset.univ.filter (fun p : Fin a × Fin b =>
          p.2 = col ∧ r ≤ p.1.val ∧ p.1.val < r + n))











/-! ### Explicit tilings for the converse -/





/-! ### Main theorem -/









end ProofsInTheBook.Chapter27


