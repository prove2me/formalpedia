-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationPairGraph_degree_sum
-- name    : Couret.STROBO2TORS.nontranslationPairGraph_degree_sum
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:08.338893+00:00
-- url     : https://prove2.me/theorems/1baba306-f6be-48b3-a6c7-77b49c3048b0
-- title:
--   The global graph degree sum counts only triple incidences
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $h=|G[2]|$, $t=|G[3]|$, and $D=|2G|$. For finite supports write $R_A$ for ordered pair-sum counts. Natural subtraction below is truncated at zero and division is integer division. The sum of graph degrees over all finite supports equals $\sum_{|A|=3}|F(A)\setminus O(A)|$.
--
--   These supports may contain zero.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/3fb45e3419d8f464ba08064afe59061c6f6f9189/research/strobo-2tors-2026-10-12/lean/Strobo2TorsUnorderedPairs.lean#L94-L119, lines 94–119; source file SHA-256 0a0634b10b5614f2bdf375961002c86d0995bc2a8ad571bab13c0dd8918d2528; theorem Couret.STROBO2TORS.nontranslationPairGraph_degree_sum

import Aesop
import Definitions.Def_Couret_Strobo2TorsUnorderedPairs_09c78b93fb82
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslationPairGraph_degree_sum :
    (∑ S : Finset G, (nontranslationPairGraph (G := G)).degree S) =
      (∑ S ∈ (tripleSupports : Finset (Finset G)),
        (nontranslatedNeighbours S).card) := by sorry








end Couret.STROBO2TORS
