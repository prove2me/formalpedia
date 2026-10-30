-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_ForestCountNS_card_rootedForests_singleton
-- name    : AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.card_rootedForests_singleton
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:49:42.396167+00:00
-- url     : https://prove2.me/theorems/124b6258-4b8c-4032-9582-226731d96ca1
-- title:
--   Parent maps toward a fixed root: the Cayley count
-- statement:
--   Let $n>1$ be a natural number and fix a root $r\in\{0,\ldots,n-1\}$. Consider parent maps from the other $n-1$ vertices to all $n$ vertices. Extend a parent map to fix $r$, and retain exactly those maps for which every vertex reaches $r$ after some finite number of iterations. Their number is
--
--   $$n^{n-2}.$$
--
--   The root is fixed before counting. The statement counts this finite functional-forest class with the source's specified finite-type structure; it does not assume a separate graph-theoretic tree representation.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/CayleyFormula.lean#L22. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCount
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Cayley's formula (arborescence form)

The `k = 1` instantiation of the generalized forest count `card_rootedForests`:
the number of trees on `n` labeled vertices rooted at a FIXED vertex — in the functional
formulation, parent maps on the remaining `n-1` vertices under which every vertex reaches the
root — equals `n^(n-2)`.  Since unrooted labeled trees on `[n]` correspond bijectively to
arborescences toward any fixed root, this is the classical Cayley count `n^(n-2)`.

This is an honest *instantiation corollary* of `ForestCountNS.Complete.card_rootedForests`
(banked separately); it is recorded here so the textbook-named statement is explicit.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.ForestCountNS

theorem AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.card_rootedForests_singleton {n : ℕ} (r : Fin n) (hn : 1 < n) :
    @Fintype.card (RootedForests ({r} : Finset (Fin n)))
        (rootedForestsFintype ({r} : Finset (Fin n))) = n ^ (n - 2) := by sorry
