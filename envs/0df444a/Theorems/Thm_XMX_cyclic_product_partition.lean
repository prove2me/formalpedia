-- Prove2me | Theorems.Thm_XMX_cyclic_product_partition
-- name    : XMX.cyclic_product_partition
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T17:03:28.016549+00:00
-- url     : https://prove2.me/theorems/6afe8d3d-c63a-43f8-824c-b356e5960091
-- title:
--   Xie–Ma–Xin Lemma 4.12: cyclic partition of product samples
-- statement:
--   For positive N and D=d+1, cyclic anchor-offset indexing is a bijection onto all D-coordinate sample-index tuples. For each fixed offset vector, every coordinate is a permutation of the N anchors. Thus the N^D indices partition into N^(D-1) coordinate-disjoint groups of N. Duplicate data values remain separate sample indices.
-- source:
--   Yaqi Xie, Will Ma, Linwei Xin, VC Theory for Inventory Policies, arXiv:2404.11509v3 (2026-02-01), Lemma 4.12, Section 4.5

import Definitions.Def_XMX_NonstationaryInventory
import Definitions.Def_XMX_CyclicPartition

set_option autoImplicit false
open MeasureTheory

namespace XMX

theorem cyclic_product_partition (N d : ℕ) (hN : 0 < N) :
    Function.Bijective (fun p : ZMod N × (Fin d → ZMod N) => cyclicTuple N d p.1 p.2) ∧
    ∀ (offset : Fin d → ZMod N) (t : Fin (d + 1)),
      Function.Bijective (fun anchor => cyclicTuple N d anchor offset t) := by sorry

end XMX
