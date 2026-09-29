-- Prove2me | Theorems.Thm_mme_MMObj_square_kronPow_iso
-- name    : mme_MMObj_square_kronPow_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:29:02.217092+00:00
-- url     : https://prove2.me/theorems/4d7f4495-86d0-40d9-8025-ac6e51bdcd0d
-- title:
--   Kronecker powers of square matrix-multiplication tensors
-- statement:
--   Let $\langle n,n,n\rangle$ be the square matrix-multiplication tensor over a field $K$. For every natural number $k$, its $k$-fold Kronecker power is isomorphic to
--
--   $$
--   \langle n,n,n\rangle^{\otimes k}
--   \cong\langle n^k,n^k,n^k\rangle.
--   $$
--
--   The statement includes $k=0$, where both sides are the tensor unit up to the canonical one-dimensional identification. It packages repeated dimension multiplication into a reusable tensor-object isomorphism needed to assemble laser-method survivor blocks.
-- source:
--   Standard multiplicativity of matrix-multiplication tensors under Kronecker product; used explicitly in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), fine-structure volume calculation on journal p. 271 (PDF p. 21); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_omega_normalize
open MME
universe u

theorem mme_MMObj_square_kronPow_iso
    {K : Type u} [Field K] (n k : ℕ) :
    TensorObj.Isomorphic (TensorObj.kronPow (MMObj K n n n) k)
      (MMObj K (n ^ k) (n ^ k) (n ^ k)) := by sorry
