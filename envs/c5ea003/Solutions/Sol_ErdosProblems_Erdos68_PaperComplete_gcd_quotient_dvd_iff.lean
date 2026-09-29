-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.gcd_quotient_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:14.17543+00:00
-- url     : https://prove2.me/submissions/83d13d7f-d133-4bb2-9fe8-2ba18c4470bf

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
theorem solution (g a t : ℤ) (hg : 0 < g) :
    g / (Int.gcd g a : ℤ) ∣ t ↔ g ∣ t * a := by
  let c : ℤ := Int.gcd g a
  have hcg : c ∣ g := Int.gcd_dvd_left g a
  have hca : c ∣ a := Int.gcd_dvd_right g a
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hcg
    omega
  have hmul : c * (g / c) = g := Int.mul_ediv_cancel' hcg
  change g / c ∣ t ↔ g ∣ t * a
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨r, hr⟩ := hca
    refine ⟨k * r, ?_⟩
    calc
      t * a = (g / c * k) * (c * r) := by rw [hk, hr]
      _ = (c * (g / c)) * (k * r) := by ring
      _ = g * (k * r) := by rw [hmul]
  · intro hga
    have hbez := Int.gcd_eq_gcd_ab g a
    have hgc : g ∣ t * c := by
      have heq : t * c =
          g * (t * Int.gcdA g a) + (t * a) * Int.gcdB g a := by
        dsimp [c]
        rw [hbez]
        ring
      rw [heq]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hga _)
    obtain ⟨k, hk⟩ := hgc
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ hc0
    calc
      c * t = t * c := by ring
      _ = g * k := hk
      _ = (c * (g / c)) * k := congrArg (fun x : ℤ => x * k) hmul.symm
      _ = c * (g / c * k) := by ring
