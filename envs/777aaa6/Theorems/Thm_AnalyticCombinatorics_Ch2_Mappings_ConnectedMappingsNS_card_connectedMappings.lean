-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_ConnectedMappingsNS_card_connectedMappings
-- name    : AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.card_connectedMappings
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:42:49.139263+00:00
-- url     : https://prove2.me/theorems/3ca6d83e-4c03-488e-881e-3d96d0dca4a2
-- title:
--   Counting connected functional graphs on a labelled finite set
-- statement:
--   Let $\mathcal F_n$ be all functions from $\{0,\ldots,n-1\}$ to itself. A point is periodic if $f^m(x)=x$ for some integer $m>0$. Define $Q(n)=\sum_{k=0}^{n-1}\prod_{j=1}^k(1-j/n)$ in the real numbers. Call $f$ connected when, for all $x,y$, there exist $i,j\in\mathbb N$ with $f^i(x)=f^j(y)$. For $n>0$,
--
--   $$|\{f\in\mathcal F_n:f\text{ connected}\}|=\sum_{k=1}^n(n-1)^{\underline{k-1}}n^{n-k}.$$
--
--   Here $a^{\underline r}$ is the descending factorial.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/ConnectedMappings.lean#L930. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ConnectedMappings
import Mathlib

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Connected random mappings

This file banks the iteration-level periodic-core facts used in the standard
cyclic-core decomposition of connected mappings.  The exact enumeration is not
completed here.
-/

open Filter Asymptotics
open scoped BigOperators Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

open AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

theorem AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.card_connectedMappings {n : ℕ} (hn : 0 < n) :
    Fintype.card {f : Fin n → Fin n // MappingConnected f}
      = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by sorry
