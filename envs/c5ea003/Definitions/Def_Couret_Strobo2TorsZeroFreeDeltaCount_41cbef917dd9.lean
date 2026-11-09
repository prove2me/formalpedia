-- Prove2me | Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
-- name    : Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:31.662246+00:00
-- url     : https://prove2.me/theorems/2edd14b0-d29c-4b6b-af18-3d9c34f881b1
-- title:
--   Unordered zero-free collision edge counts by symmetric difference
-- statement:
--   For a finite abelian additive group G with decidable equality and any natural k, this bundle defines three natural counts as edgeFinset cardinalities after restricting both endpoint supports to avoid zero. zeroFreeSquareDeltaPairCount uses the union squareDeltaGraph k, zeroFreeOrdinaryDeltaPairCount uses ordinaryDeltaGraph k, and zeroFreeNontranslationDeltaPairCount uses nontranslationDeltaGraph k. Endpoints are distinct three-element finite subsets of G, and their symmetric difference has cardinality k. Ordinary edges relate supports by a translation u with u+u=0; nontranslation edges join equal labelled ordered-square supports with no ambient translation between them. Edges are unordered and retain the labelled group elements; there is no quotient by group automorphisms or simultaneous translations. The definitions apply to every k and to small groups, with empty edge sets counted as zero. They contain no closed formula for these counts.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeDeltaCount.lean; source file SHA-256 302023407fa92aa36bd7bd7c4099764736ee28c1a899b531c3a1166252b8c4b2

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact unordered collision counts by symmetric difference after excluding zero
from both three-element supports. The proof transfers each translation-stable
branch by incidence counting. All subtractions and divisions are in Nat.
Historical unrestricted counts remain unchanged.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite

variable [Fintype G]







/-- All unordered zero-free equal-square pairs, with labelled group elements. -/
noncomputable def zeroFreeSquareDeltaPairCount (k : ℕ) : ℕ :=
  (zeroFreeGraph (squareDeltaGraph (G := G) k)).edgeFinset.card

noncomputable def zeroFreeOrdinaryDeltaPairCount (k : ℕ) : ℕ :=
  (zeroFreeGraph (ordinaryDeltaGraph (G := G) k)).edgeFinset.card

noncomputable def zeroFreeNontranslationDeltaPairCount (k : ℕ) : ℕ :=
  (zeroFreeGraph (nontranslationDeltaGraph (G := G) k)).edgeFinset.card

















































end Finite

end Couret.STROBO2TORS


