-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceInnerZ_qPochhammer
-- name    : ErdosProblems.Erdos1049.PaperR12.sourceInnerZ_qPochhammer
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:53:29.983125+00:00
-- url     : https://prove2.me/theorems/91eeb3dc-4755-42a0-af17-f7d75a539c36
-- title:
--   Source inner z q pochhammer
-- statement:
--   For the displayed natural indices a≥1 and v≥1 in the commutative source ring, multiplying the free-variable finite inner transform by (q;q)_(a−1) gives its explicit q-binomial/Pochhammer sum.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceFiniteTransformR12.lean#L21-L75
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! # The missing free-variable finite source transform
The variable z is independent of q.
Consequently the identity can be specialised in any commutative ring,
including a Laurent polynomial ring; it is not limited to z=q^alpha with
alpha a natural number. The proof uses only two finite q-binomial expansions.
-/
open Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]

open ErdosProblems.Erdos1049.PaperR12

set_option maxHeartbeats 500000 in

theorem ErdosProblems.Erdos1049.PaperR12.sourceInnerZ_qPochhammer (q z : R) {a d v : ℕ}
    (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer q q (a - 1) * sourceInnerZ q z a d v =
      ∑ h ∈ range a,
        (-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) *
          gaussBinom q (a - 1) h * qPochhammer q (z * q ^ h) (v - 1) := by sorry
