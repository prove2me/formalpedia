-- Prove2me | Theorems.Thm_SymplecticMatrix_lie_elemS_elemX
-- name    : SymplecticMatrix.lie_elemS_elemX
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T15:44:02.092398+00:00
-- url     : https://prove2.me/theorems/c6f51cbd-069b-4e46-b354-8d9dea7864c8
-- title:
--   $[S_{i,i}, X_{i,j}] = S_{i,j}$ for $i \ne j$
-- statement:
--   Let $R$ be a commutative ring and let $\mathfrak{sp}_{2l}(R)$ be the symplectic Lie algebra, realized as the matrices that are skew-adjoint for the canonical alternating form
--
--   $$
--   J=\begin{pmatrix}0&-I\\ I&0\end{pmatrix},
--   \qquad\text{that is}\qquad A^{\mathsf T}J=-JA .
--   $$
--
--   This theorem is the bracket identity that reduces the lower-left family to its diagonal part. For $i\ne j$,
--
--   $$
--   \bigl[S_{i,i},\,X_{i,j}\bigr]=S_{i,j} .
--   $$
--
--   The computation is short. Since $S_{i,i}=E_{l+i,i}$ and $X_{i,j}=E_{i,j}-E_{l+j,l+i}$,
--
--   $$
--   S_{i,i}X_{i,j}=E_{l+i,j},\qquad X_{i,j}S_{i,i}=-E_{l+j,i},
--   $$
--
--   the other two products vanishing for index reasons, so the commutator is $E_{l+i,j}+E_{l+j,i}$, which is precisely $S_{i,j}$ when $i\ne j$.
--
--   The identity is what makes the smaller generating set sufficient. The full spanning family of $\mathfrak{sp}_{2l}(R)$ contains all $S_{i,j}$, but only the diagonal ones need to be taken as generators: the rest are recovered by bracketing against the $\mathfrak{gl}_l$ part. On the diagonal the same computation gives $2S_{i,i}$ rather than $S_{i,i}$, which is why $i\ne j$ is required and why the diagonal elements are kept among the generators.
-- source:
--   Standard structure theory of the classical Lie algebra of type C_l; see e.g. J. E. Humphreys, Introduction to Lie Algebras and Representation Theory, Springer GTM 9, Section 1.2 (type C_l). Mathlib provides only the definition LieAlgebra.Symplectic.sp in Mathlib/Algebra/Lie/Classical.lean, with no membership criterion, block description, spanning family or generating set.

import Definitions.Def_symplectic_block_generators

namespace SymplecticMatrix

open Matrix

variable {l : ℕ} {R : Type*} [CommRing R]

theorem lie_elemS_elemX (i j : Fin l) (hij : i ≠ j) :
    ⁅(elemS i i : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R),
      (elemX i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)⁆ = elemS i j := by sorry

end SymplecticMatrix
