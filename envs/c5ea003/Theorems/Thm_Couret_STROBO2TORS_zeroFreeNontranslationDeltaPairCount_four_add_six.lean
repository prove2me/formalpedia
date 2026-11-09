-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeNontranslationDeltaPairCount_four_add_six
-- name    : Couret.STROBO2TORS.zeroFreeNontranslationDeltaPairCount_four_add_six
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:58:36.3071+00:00
-- url     : https://prove2.me/theorems/687f2d9b-85ca-4c58-8a91-7b0fd1cc88f6
-- title:
--   All unordered nontranslation collisions are counted by two distances
-- statement:
--   Let $G$ be an abelian group. A nontranslation collision consists of two zero-free three-element supports with equal ordered-square counts, with neither obtained from the other by any ambient translation. Assume $G$ finite. With $c_k$ the unordered distance-$k$ count and $P^{\rm unord}$ the full unordered collision family,
--
--   $$c_4+c_6=|P^{\rm unord}|.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeCompatibility.lean#L90-L100, lines 90–100; source file SHA-256 d1d30fcfd3315a8e79e6308cfbe94a9cf53fec89005d1286ef2baa5e566230ba; theorem Couret.STROBO2TORS.zeroFreeNontranslationDeltaPairCount_four_add_six

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_adj_iff
import Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_delta_partition
import Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_eq_twice
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact compatibility with the historical zero-free nontranslation-pair count.
This identifies the counted objects, not merely their numerical formulas:
the old family is the disjoint union of the new delta-four and delta-six
families. All historical definitions and proofs are retained unchanged.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem zeroFreeNontranslationDeltaPairCount_four_add_six :
    zeroFreeNontranslationDeltaPairCount (G := G) 4 +
      zeroFreeNontranslationDeltaPairCount (G := G) 6 =
      (nontranslationPairs : Finset (Finset (Finset G))).card := by sorry



end Finite

end Couret.STROBO2TORS
