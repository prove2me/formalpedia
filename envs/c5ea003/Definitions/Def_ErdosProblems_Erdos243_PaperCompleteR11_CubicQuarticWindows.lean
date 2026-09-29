-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:24:09.576701+00:00
-- url     : https://prove2.me/theorems/25a940a6-502e-4396-b134-86d3bd5ccee4
-- title:
--   Cubic window expressions and residue predicates
-- statement:
--   Defines three cubic window expressions and the predicates CubicQuarticNonresidue and CubicQuarticWitness.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicQuarticWindows.lean#L1-L203
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

   
                                                 

                                                                              
                                                    
                         
                                                                            
                                                                            
  

namespace ErdosProblems.Erdos243.PaperCompleteR11





/-- Values at distances two to the left, one to the left and one to the right
of a root of a depressed cubic, after subtracting its root equation. -/
def cubicLeftTwo {R : Type*} [CommRing R] (r : R) : R := -6 * (r - 1) ^ 2

def cubicLeftOne {R : Type*} [CommRing R] (r : R) : R := -3 * r * (r - 1)

def cubicRightOne {R : Type*} [CommRing R] (r : R) : R := 3 * r * (r + 1)

/-- A finite-field certificate that the four-term word cannot occur. -/
def CubicQuarticNonresidue {R : Type*} [CommRing R] (r : R) : Prop :=
  ∀ d : R, (d * (d + cubicLeftOne r)) ^ 2 ≠
    -(cubicLeftTwo r) ^ 2 * cubicLeftOne r * cubicRightOne r

/-- A concrete coefficient ratio is covered when it has an obstructed root. -/
def CubicQuarticWitness (p : ℕ) (ρ : ZMod p) : Prop :=
  ∃ r : ZMod p, r ^ 3 - r + 6 * ρ = 0 ∧ CubicQuarticNonresidue r











end ErdosProblems.Erdos243.PaperCompleteR11


