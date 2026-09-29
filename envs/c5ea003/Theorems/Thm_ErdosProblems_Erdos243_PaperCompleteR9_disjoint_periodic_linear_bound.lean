-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR9_disjoint_periodic_linear_bound
-- name    : ErdosProblems.Erdos243.PaperCompleteR9.disjoint_periodic_linear_bound
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:34:58.134183+00:00
-- url     : https://prove2.me/theorems/2ae86f1e-4983-4c1b-acb6-bb6eb8f92aae
-- title:
--   Linear count bound from periodic hits
-- statement:
--   If s is positive, L ≤ s and every block beginning at r + sk contains a member of E in its first L positions, then X ≤ s times the exception count of E below X plus r + s for every X.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR9/PolynomialCorrections.lean#L42-L66
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
Correct phase-specific modulo-seven obstructions, a sharp
one-in-seven disjoint-block counting certificate, and exact counterexamples
to the stronger phase-free statement in the supplied manuscript.
-/

open ErdosProblems.Erdos243.PaperCompleteR9

theorem ErdosProblems.Erdos243.PaperCompleteR9.disjoint_periodic_linear_bound (E : Set ℕ) (r s L : ℕ)
    (hs : 0 < s) (hL : L ≤ s)
    (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E) :
    ∀ X : ℕ, X ≤ s * exceptionCount E X + (r + s) := by sorry
