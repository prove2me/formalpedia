-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
-- name    : ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:52:48.531764+00:00
-- url     : https://prove2.me/theorems/32cea3b8-1b10-46f8-b429-2c306317b005
-- title:
--   Exception sets and their finite counts
-- statement:
--   Defines the finite set of exceptions in E below a cutoff X and its cardinality.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR9/PolynomialCorrections.lean#L1-L242
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
Correct phase-specific modulo-seven obstructions, a sharp
one-in-seven disjoint-block counting certificate, and exact counterexamples
to the stronger phase-free statement in the supplied manuscript.
-/
namespace ErdosProblems.Erdos243.PaperCompleteR9

noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)

noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card

























end ErdosProblems.Erdos243.PaperCompleteR9


