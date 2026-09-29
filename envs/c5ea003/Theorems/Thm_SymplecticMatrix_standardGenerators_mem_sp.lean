-- Prove2me | Theorems.Thm_SymplecticMatrix_standardGenerators_mem_sp
-- name    : SymplecticMatrix.standardGenerators_mem_sp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T15:43:51.332274+00:00
-- url     : https://prove2.me/theorems/6ae33921-f3c4-43d5-9430-d308ab7e02b8
-- title:
--   The standard families lie in $\mathfrak{sp}_{2l}(R)$
-- statement:
--   Let $R$ be a commutative ring and let $\mathfrak{sp}_{2l}(R)$ be the symplectic Lie algebra, realized as the matrices that are skew-adjoint for the canonical alternating form
--
--   $$
--   J=\begin{pmatrix}0&-I\\ I&0\end{pmatrix},
--   \qquad\text{that is}\qquad A^{\mathsf T}J=-JA .
--   $$
--
--   This theorem records that the three standard families really are symplectic. With $\Sigma_{i,j}$ the symmetric elementary matrix — $E_{i,i}$ on the diagonal and $E_{i,j}+E_{j,i}$ off it — the families are
--
--   $$
--   X_{i,j}=\begin{pmatrix} E_{i,j} & 0\\ 0 & -E_{i,j}^{\mathsf T}\end{pmatrix},\qquad
--   T_{i,j}=\begin{pmatrix} 0 & \Sigma_{i,j}\\ 0 & 0\end{pmatrix},\qquad
--   S_{i,j}=\begin{pmatrix} 0 & 0\\ \Sigma_{i,j} & 0\end{pmatrix},
--   $$
--
--   and each lies in $\mathfrak{sp}_{2l}(R)$.
--
--   Each is a single application of the block criterion. For $X_{i,j}$ the lower-right block is by construction minus the transpose of the upper-left one and the off-diagonal blocks vanish; for $T_{i,j}$ and $S_{i,j}$ the diagonal blocks vanish and the one nonzero off-diagonal block is symmetric by construction.
--
--   Elementary as it is, this is the statement that gives the three families their meaning: without it, any assertion quantifying over presentations by these matrices would be vacuous.
-- source:
--   Standard structure theory of the classical Lie algebra of type C_l; see e.g. J. E. Humphreys, Introduction to Lie Algebras and Representation Theory, Springer GTM 9, Section 1.2 (type C_l). Mathlib provides only the definition LieAlgebra.Symplectic.sp in Mathlib/Algebra/Lie/Classical.lean, with no membership criterion, block description, spanning family or generating set.

import Definitions.Def_symplectic_block_generators

namespace SymplecticMatrix

open Matrix

variable {l : ℕ} {R : Type*} [CommRing R]

theorem standardGenerators_mem_sp (i j : Fin l) :
    (elemX i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        ∈ LieAlgebra.Symplectic.sp (Fin l) R ∧
      (elemT i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        ∈ LieAlgebra.Symplectic.sp (Fin l) R ∧
      (elemS i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        ∈ LieAlgebra.Symplectic.sp (Fin l) R := by sorry

end SymplecticMatrix
