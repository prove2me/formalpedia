-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:26:09.568982+00:00
-- url     : https://prove2.me/theorems/e04f7177-aa69-460f-89f7-76995c04dcfe
-- title:
--   Local primality instance for seven
-- statement:
--   This bundle retains a local Lean instance certifying that 7 is prime. It does not state a public theorem.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicQuarticCertificates.lean#L1-L243
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
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


local instance instFactPrimeOfNatNat_erdosProblems_1 : Fact (Nat.Prime 7) := ⟨by decide⟩








































end ErdosProblems.Erdos243.PaperCompleteR11


