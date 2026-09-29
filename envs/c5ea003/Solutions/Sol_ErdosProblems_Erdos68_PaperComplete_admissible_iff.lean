-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.admissible_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:04:13.689013+00:00
-- url     : https://prove2.me/submissions/0677b5d3-abe0-4292-8a02-a8b75a24f1db

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
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
import Mathlib.Tactic.Abel
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
theorem solution (f : ℕ →₀ ℤ) :
    Admissible f ↔ f 0 = 0 ∧ f 1 = 0 := by
  classical
  constructor
  · intro h
    constructor
    · by_contra hn
      have := h 0 (Finsupp.mem_support_iff.mpr hn)
      omega
    · by_contra hn
      have := h 1 (Finsupp.mem_support_iff.mpr hn)
      omega
  · rintro ⟨h0, h1⟩ n hn
    have hne := Finsupp.mem_support_iff.mp hn
    by_contra h
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> contradiction
