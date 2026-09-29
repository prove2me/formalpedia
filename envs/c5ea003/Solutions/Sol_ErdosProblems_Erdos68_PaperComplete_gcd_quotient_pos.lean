-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.gcd_quotient_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:16:41.846009+00:00
-- url     : https://prove2.me/submissions/2ddf9a8d-4e36-4c7d-a59b-48db1834c8a0

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

   
                                                                  
                                                                              
  

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (g a : ℤ) (hg : 0 < g) :
    0 < g / (Int.gcd g a : ℤ) := by
  have hd : (Int.gcd g a : ℤ) ∣ g := Int.gcd_dvd_left g a
  have hmul := Int.mul_ediv_cancel' hd
  have hc : (0 : ℤ) ≤ Int.gcd g a := by positivity
  by_contra h
  have hq : g / (Int.gcd g a : ℤ) ≤ 0 := by omega
  have hprod := mul_nonpos_of_nonneg_of_nonpos hc hq
  omega
