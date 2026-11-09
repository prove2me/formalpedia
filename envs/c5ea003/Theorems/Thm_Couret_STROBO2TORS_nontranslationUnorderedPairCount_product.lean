-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nontranslationUnorderedPairCount_product
-- name    : Couret.STROBO2TORS.nontranslationUnorderedPairCount_product
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:54.199421+00:00
-- url     : https://prove2.me/theorems/0eb65d1c-327a-4997-95ef-5a5a0368d305
-- title:
--   A product formula for actual unordered nontranslation pairs
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $h=|G[2]|$, $t=|G[3]|$, and $D=|2G|$. For finite supports write $R_A$ for ordered pair-sum counts. Natural subtraction below is truncated at zero and division is integer division. Let $U$ count unordered pairs of triple supports with equal square and no ambient translation. Then
--
--   $$U=Dh^2(h-1)\frac{t-1}{2}.$$
--
--   The last factor counts nonzero three-torsion sign pairs.
--
--   These supports may contain zero.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/3fb45e3419d8f464ba08064afe59061c6f6f9189/research/strobo-2tors-2026-10-12/lean/Strobo2TorsUnorderedPairs.lean#L146-L173, lines 146–173; source file SHA-256 0a0634b10b5614f2bdf375961002c86d0995bc2a8ad571bab13c0dd8918d2528; theorem Couret.STROBO2TORS.nontranslationUnorderedPairCount_product

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
import Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum_numeric
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Theorems.Thm_Couret_STROBO2TORS_nontranslationPairGraph_degree_sum
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem nontranslationUnorderedPairCount_product :
    nontranslationUnorderedPairCount (G := G) =
      (doublingImages : Finset G).card *
        (twoTorsion : Finset G).card *
        (twoTorsion : Finset G).card *
        ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card := by sorry


end Couret.STROBO2TORS
