-- Prove2me | Theorems.Thm_mme_schonhage_pan_direct_sum
-- name    : mme_schonhage_pan_direct_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T22:56:26.341154+00:00
-- url     : https://prove2.me/theorems/a2a6e538-44d1-4555-b4b3-b89703fbbbb5
-- title:
--   Pan–Winograd triple direct sum has asymptotic rank at most 156
-- statement:
--   Over every field $K$, the tensor asymptotic rank of
--
--   $$
--   \langle1,5,22\rangle\oplus\langle11,2,5\rangle\oplus\langle10,11,1\rangle
--   $$
--
--   is at most $156$.
--
--   This is the asymptotic-rank form of the Pan–Winograd approximate-rank construction and is the direct input required by Schönhage's asymptotic sum inequality. The underlying degeneration is kept as a separate milestone so that the source construction is visible and independently auditable.
-- source:
--   Francesco Romani, Some Properties of Disjoint Sums of Tensors Related to Matrix Multiplication, CNR Nota Interna B80-4, February 1980, printed p. 6 (PDF p. 7), specialized to n=11 and k=5; A. Schönhage, Partial and Total Matrix Multiplication, SIAM J. Comput. 10(3), 1981, DOI 10.1137/0210032.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_tensor_rank
universe u
open MME

theorem mme_schonhage_pan_direct_sum {K : Type u} [Field K] :
    tensorAsymptoticRank
      (TensorObj.bigAdd ![
        MMObj K 1 5 22,
        MMObj K 11 2 5,
        MMObj K 10 11 1]) ≤ 156 := by sorry
