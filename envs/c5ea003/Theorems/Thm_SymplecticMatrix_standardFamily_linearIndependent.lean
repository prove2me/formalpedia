-- Prove2me | Theorems.Thm_SymplecticMatrix_standardFamily_linearIndependent
-- name    : SymplecticMatrix.standardFamily_linearIndependent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T17:01:49.057346+00:00
-- url     : https://prove2.me/theorems/b160bccb-611e-4ca6-8d51-e0b4608cb1ff
-- title:
--   The standard family of $\mathfrak{sp}_{2l}(R)$ is linearly independent
-- statement:
--   Let $R$ be a commutative ring. Index the standard families of $\mathfrak{sp}_{2l}(R)$ by
--
--   $$
--   (i,j)\in\{1,\dots,l\}^2 \quad\text{for } X_{i,j},
--   \qquad
--   i\le j \quad\text{for } T_{i,j} \text{ and } S_{i,j},
--   $$
--
--   so that the index set is the disjoint union of $\{1,\dots,l\}^2$ with two copies of the ordered pairs. The corresponding family of matrices is linearly independent over $R$.
--
--   Together with the fact that these matrices span $\mathfrak{sp}_{2l}(R)$, this makes them a basis, of cardinality
--
--   $$
--   l^2+2\cdot\frac{l(l+1)}{2}=l(2l+1),
--   $$
--
--   the familiar dimension of the symplectic Lie algebra of rank $l$.
--
--   **Why the statement is not automatic.** The three families occupy different blocks — $X$ the diagonal ones, $T$ the upper-right, $S$ the lower-left — so no relation can mix them, and independence decouples into three separate questions. Within the $X$ family the matrices are essentially matrix units and independence is immediate. Within the $T$ and $S$ families it is the restriction to $i\le j$ that does the work: without it the family would repeat, since $\Sigma_{i,j}=\Sigma_{j,i}$. Reading the entry in position $(i,j)$ with $i\le j$ isolates the coefficient of $\Sigma_{i,j}$, because the mirrored contribution of $\Sigma_{j,i}$ is excluded by the ordering convention.
--
--   The statement holds over any commutative ring, with no invertibility assumption on $2$; this is again due to the convention $\Sigma_{i,i}=E_{i,i}$ rather than $2E_{i,i}$.
-- source:
--   Standard structure theory of the classical Lie algebra of type C_l; see e.g. J. E. Humphreys, Introduction to Lie Algebras and Representation Theory, Springer GTM 9, Section 1.2 (type C_l), where this family is exhibited as a basis and the dimension l(2l+1) is read off from it. Mathlib provides only the definition LieAlgebra.Symplectic.sp in Mathlib/Algebra/Lie/Classical.lean, with no basis or dimension.

import Definitions.Def_symplectic_block_generators

namespace SymplecticMatrix

open Matrix

theorem standardFamily_linearIndependent (l : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R
      (Sum.elim (fun p : Fin l × Fin l =>
          (elemX p.1 p.2 : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R))
        (Sum.elim (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemT p.1.1 p.1.2)
          (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemS p.1.1 p.1.2))) := by sorry

end SymplecticMatrix
