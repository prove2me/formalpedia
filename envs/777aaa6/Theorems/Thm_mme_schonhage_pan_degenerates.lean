-- Prove2me | Theorems.Thm_mme_schonhage_pan_degenerates
-- name    : mme_schonhage_pan_degenerates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T22:56:13.16028+00:00
-- url     : https://prove2.me/theorems/8ba1453b-1b69-4daf-a554-f77ef689d5f5
-- title:
--   Pan–Winograd triple direct sum has border rank at most 156
-- statement:
--   Over every field $K$, the direct sum
--
--   $$
--   \langle1,5,22\rangle\oplus\langle11,2,5\rangle\oplus\langle10,11,1\rangle
--   $$
--
--   is a degeneration of the order-three diagonal unit tensor $I_{156}$. Equivalently, this three-summand tensor has border rank at most $156$.
--
--   This is the $n=11$, $k=5$ specialization of the Pan–Winograd construction recorded by Romani: $\underline R(t\oplus t'\oplus t'')\le2(n+2)(k+1)$ for $t=\langle1,k,2n\rangle$, $t'=\langle n,2,k\rangle$, and $t''=\langle2k,n,1\rangle$.
--
--   **Formalization Note** `Degenerates` existentially quantifies the leading order of the polynomial family. The statement therefore records exactly the source's approximate-rank bound without imposing an unsupported degeneration order.
-- source:
--   Francesco Romani, Some Properties of Disjoint Sums of Tensors Related to Matrix Multiplication, CNR Nota Interna B80-4, February 1980, printed p. 6 (PDF p. 7), https://iris.cnr.it/retrieve/7f08fe3e-3ef4-42b1-b84f-82ba5e09c61a/prod_421763-doc_149822.pdf; A. Schönhage, Partial and Total Matrix Multiplication, SIAM J. Comput. 10(3), 1981, abstract (arbitrary-field setting), DOI 10.1137/0210032.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
universe u
open MME

theorem mme_schonhage_pan_degenerates {K : Type u} [Field K] :
    Degenerates
      (TensorObj.bigAdd ![
        MMObj K 1 5 22,
        MMObj K 11 2 5,
        MMObj K 10 11 1])
      (TensorObj.diagObj K 3 156) := by sorry
