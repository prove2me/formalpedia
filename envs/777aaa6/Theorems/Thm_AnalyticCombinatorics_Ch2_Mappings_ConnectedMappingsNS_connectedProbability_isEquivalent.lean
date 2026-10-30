-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_ConnectedMappingsNS_connectedProbability_isEquivalent
-- name    : AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.connectedProbability_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:42:42.15863+00:00
-- url     : https://prove2.me/theorems/2f502aa1-fa70-4a4a-a046-23398b480471
-- title:
--   Asymptotic probability that a uniform self-map is connected
-- statement:
--   Let $\mathcal F_n$ be all functions from $\{0,\ldots,n-1\}$ to itself. A point is periodic if $f^m(x)=x$ for some integer $m>0$. Define $Q(n)=\sum_{k=0}^{n-1}\prod_{j=1}^k(1-j/n)$ in the real numbers. Let $C_n$ count functions whose every pair of vertices has forward iterates that meet. As $n\to\infty$,
--
--   $$\frac{C_n}{n^n}\sim\sqrt{\frac{\pi}{2n}}.$$
--
--   This probability is the finite count divided by the number $n^n$ of all functions; the displayed asymptotic concerns natural $n$ tending to infinity.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/ConnectedMappings.lean#L1058. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.connectedProbability_isEquivalent :
    (fun n : ℕ => (Fintype.card {f : Fin n → Fin n // MappingConnected f} : ℝ) / n ^ n)
      ~[atTop] (fun n : ℕ => Real.sqrt (Real.pi / (2 * n))) := by sorry
