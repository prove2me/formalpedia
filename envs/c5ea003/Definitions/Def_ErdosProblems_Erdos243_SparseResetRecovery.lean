-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_SparseResetRecovery
-- name    : ErdosProblems_Erdos243_SparseResetRecovery
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:47:34.486208+00:00
-- url     : https://prove2.me/theorems/e7305824-acf6-4d7a-b05c-a9ce56b1cb46
-- title:
--   Negative relative mass
-- statement:
--   For C:N→N and E:N→Z, defines delta_n=abs(min(E_n,0))/C_n=max(-E_n,0)/C_n in the reals. Positivity of C and the recurrence C_(n+1)=C_n-E_n are hypotheses of the separate stabilization theorem, not restrictions built into this definition.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/SparseResetRecovery.lean#L1-L720
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_SparseResetRecovery is the versioned native alias of original module ErdosProblems.Erdos243.SparseResetRecovery.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős #243: sparse reset recovery

This module isolates the order-theoretic recovery forest behind dynamically
reduced reciprocal-tail orbits.  It also gives a division-free finite-product
bound for the full reset payment on a recovery interval.

The declarations do not exclude the unrestricted divergent-negative-mass
branch and therefore do not prove Erdős #243.
-/

namespace ErdosProblems.Erdos243

open scoped BigOperators

/-! ## Recovery intervals -/



















/-! ## Division-free payment bounds -/











/-! ## A checked endpoint consumer -/



/-- The normalized negative mass of an integral tail step. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n









/-! ## Scalar finite mass, without normalised vanishing

Type B r2 (file 05, Proposition J) observed that the product bound already
caps `C_n`, so a strict integer rise costs a definite relative mass `≥ 1/K`
and only finitely many rises can occur.  After the last rise the tail is
nonincreasing, hence eventually constant by
`antitone_nat_eventually_constant`.  Normalised vanishing is not used. -/







end ErdosProblems.Erdos243


