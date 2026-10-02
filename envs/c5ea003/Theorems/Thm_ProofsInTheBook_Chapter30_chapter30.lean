-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter30_chapter30
-- name    : ProofsInTheBook.Chapter30.chapter30
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:27:17.620151+00:00
-- url     : https://prove2.me/theorems/7a86d2f9-260e-4d7c-9600-617cd77fb78d
-- title:
--   Conditional LGV-type identity for a finite marked-family system
-- statement:
--   Let n be a natural number, let V have decidable equality, and let R be a commutative ring. Suppose a PathCountSystem is supplied: a vertex weight $v:V\to R$; finite types $P_{ij}$ with weights $a:P_{ij}\to R$ for every pair $i,j\in\{0,\ldots,n-1\}$; a bijection
--   $$E:\coprod_{\sigma\in S_n}\prod_i P_{\sigma(i),i}\;\longrightarrow\;\mathcal F_n(V);$$
--   and, for every choice $(\sigma,p)$, the compatibility identity
--   $$w_v(E(\sigma,p))=\operatorname{sgn}(\sigma)\prod_i a(p_i).$$
--   Here $\mathcal F_n(V)$ is the defined disjoint union of pairwise vertex-disjoint list families and marked bad list data, and $w_v$ is its specified signed vertex-product weight. Set $M_{ij}=\sum_{p\in P_{ij}}a(p)$. Assume explicitly that the entire type $\mathcal F_n(V)$ is finite.
--
--   Assume also decidable equality on $\mathcal F_n(V)$ and that the additive group of R is torsion-free. Then
--   $$\det M=\sum_{\substack{F\in\mathcal F_n(V)\\\neg\mathrm{isBad}(F)}}w_v(F).$$
--   Here isBad selects the marked bad constructor; its complement consists exactly of good families, whose distinct vertex lists are disjoint including endpoints. The sum remains signed; no hypothesis restricts surviving permutations to the identity.
--
--   This is a conditional algebraic identity for the supplied finite system and its weight-preserving bijection. The underlying lists have unrestricted length and no graph-edge, source, sink, or lattice-step constraints. For positive n and nonempty V, unrestricted list families are not a finite geometric path space. The source explicitly leaves bounded or geometric path infrastructure, grid applications, and the hook-length formula unresolved.
-- source:
--   Exact repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L567. PathCountSystem hypotheses: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L435. Explicit scope limitation: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter30.lean#L578. Repository topic: “Lattice paths and determinants.” No edition-specific chapter mapping or geometric application is asserted.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter30
open ProofsInTheBook.Chapter30
open Matrix BigOperators

theorem ProofsInTheBook.Chapter30.chapter30 {n : ℕ} {V R : Type*} [DecidableEq V]
    [Fintype (LGVFamily n V)] [DecidableEq (LGVFamily n V)]
    [CommRing R] [IsAddTorsionFree R]
    (S : PathCountSystem n V R) :
    S.matrix.det =
      ∑ F ∈ Finset.univ.filter (fun F : LGVFamily n V => ¬ ProofsInTheBook.Chapter30.LGVFamily.isBad F),
        ProofsInTheBook.Chapter30.LGVFamily.signedWeight S.vertexWeight F := by sorry
