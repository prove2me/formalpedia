-- Prove2me | Theorems.Thm_SymplecticMatrix_exists_basis_standardFamily
-- name    : SymplecticMatrix.exists_basis_standardFamily
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T01:52:14.914776+00:00
-- url     : https://prove2.me/theorems/f21400f6-51cb-444e-8b11-0b8f3dcdd1a1
-- title:
--   The standard block generators form a basis of $\mathfrak{sp}_{2\ell}$
-- statement:
--   Over a field, the symplectic Lie algebra $\mathfrak{sp}_{2\ell}$ has a basis consisting of the standard block generators: the $\ell^2$ elements
--
--   $$
--   X_{i,j}=\begin{pmatrix}E_{ij}&0\\0&-E_{ij}^{\mathsf T}\end{pmatrix}\quad (i,j\in\{1,\dots,\ell\}),
--   $$
--
--   together with the upper-right generators $T_{i,j}$ and the lower-left generators $S_{i,j}$, each taken once for every unordered pair $i\le j$.
--
--   **Role.** The two published facts about this family --- that it spans $\mathfrak{sp}_{2\ell}$ and that it is linearly independent --- are what one proves, but a *basis* is what one uses. Having it as a `Module.Basis` is what allows a linear map out of $\mathfrak{sp}_{2\ell}$ to be defined by prescribing its values on these generators, and what reduces the verification that such a map respects the bracket to a finite list of identities between the prescribed values. That is precisely the shape of the construction of a polynomial representation of $\mathfrak{sp}_{2\ell}$ from displayed differential operators.
--
--   The indexing is by unordered pairs for the symmetric blocks and by ordered pairs for the diagonal block, which is exactly the redundancy in the naive spanning family: $T_{i,j}=T_{j,i}$ and $S_{i,j}=S_{j,i}$, since the corresponding matrix blocks are symmetric, while the $X_{i,j}$ are genuinely distinct for distinct ordered pairs. Counting gives $\ell^2+2\cdot\binom{\ell+1}{2}=\ell(2\ell+1)$, the known dimension.
-- source:
--   Standard structure theory of the classical Lie algebras; the block description of sp is the one used throughout Y. Chen and H. Tan, Simple sp_{2l}(C)-modules which are free over an abelian nilradical, Journal of Algebra 697 (2026), 341-372. Mathlib defines sp but records no basis for it.

import Definitions.Def_symplectic_block_generators

namespace SymplecticMatrix

open Matrix

theorem exists_basis_standardFamily (l : ℕ) (R : Type*) [Field R] :
    ∃ B : Module.Basis
        ((Fin l × Fin l) ⊕
          ({p : Fin l × Fin l // p.1 ≤ p.2} ⊕ {p : Fin l × Fin l // p.1 ≤ p.2}))
        R (LieAlgebra.Symplectic.sp (Fin l) R),
      ∀ i, ((B i : LieAlgebra.Symplectic.sp (Fin l) R) :
            Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)
        = Sum.elim (fun p : Fin l × Fin l => elemX p.1 p.2)
            (Sum.elim (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemT p.1.1 p.1.2)
              (fun p : {p : Fin l × Fin l // p.1 ≤ p.2} => elemS p.1.1 p.1.2)) i := by sorry

end SymplecticMatrix
