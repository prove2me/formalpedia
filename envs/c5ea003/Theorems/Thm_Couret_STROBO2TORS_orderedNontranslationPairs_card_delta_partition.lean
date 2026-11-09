-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_delta_partition
-- name    : Couret.STROBO2TORS.orderedNontranslationPairs_card_delta_partition
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:21.084357+00:00
-- url     : https://prove2.me/theorems/ac5e5a32-9461-4848-83fe-83ce9ec7d78c
-- title:
--   Ordered nontranslation pairs partition into distances four and six
-- statement:
--   Let $G$ be an abelian group. A nontranslation collision consists of two zero-free three-element supports with equal ordered-square counts, with neither obtained from the other by any ambient translation. Assume $G$ finite and let $P$ be the ordered nontranslation collision family. Then
--
--   $$|P_4|+|P_6|=|P|,$$
--
--   where $P_k$ retains distance $k$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeCompatibility.lean#L58-L88, lines 58–88; source file SHA-256 d1d30fcfd3315a8e79e6308cfbe94a9cf53fec89005d1286ef2baa5e566230ba; theorem Couret.STROBO2TORS.orderedNontranslationPairs_card_delta_partition

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
import Theorems.Thm_Couret_STROBO2TORS_NontranslationCollision_ne
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_two_iff
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_cases
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

theorem orderedNontranslationPairs_card_delta_partition :
    ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
      (fun p => (p.1 ∆ p.2).card = 4)).card +
    ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
      (fun p => (p.1 ∆ p.2).card = 6)).card =
      (orderedNontranslationPairs : Finset (Finset G × Finset G)).card := by sorry





end Finite

end Couret.STROBO2TORS
