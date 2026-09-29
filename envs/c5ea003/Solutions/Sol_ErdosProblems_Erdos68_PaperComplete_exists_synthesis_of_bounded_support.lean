-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.exists_synthesis_of_bounded_support
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:20:52.292244+00:00
-- url     : https://prove2.me/submissions/9a1dca5f-d358-48dc-8800-0e3a03215b4b

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Theorems.Thm_ErdosProblems_Erdos68_isolatedChannelUnit_of_two_le
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_isolated_unit_outside
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_add
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelSynthesis_single
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
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

/-!
# Full integral coordinate theorem

Short label res:divisor-channel-coordinates. The supplied library proves the
isolated moment/channel values, but does not prove spanning and uniqueness.
Here the auxiliary index 1 is represented by coordinate 0, and coordinate j>0
represents U_(j+1). Thus coordinates have type ℕ →₀ ℤ with no constrained
coordinate. The target coefficient vectors satisfy f 0 = 0, exactly the
paper's index convention n≥1 before its later restriction to n≥2.

The proof supplies spanning by triangular elimination, independence by the
moment/channel observables, and the explicit coefficient formula. This is
stronger than checking finitely many example matrices.
STATUS: compiled proof candidate. No axioms or proof placeholders.
-/

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp



lemma isolated_unit_leading {n : ℕ} (hn : 2 ≤ n) :
    isolatedChannelUnit n n = -1 := by
  have hpred : n - 1 ≠ n := by omega
  have hT : adjacentDifference n n = -1 := by
    simp [adjacentDifference, hpred, Ne.symm hpred]
  rw [isolatedChannelUnit_of_two_le hn, Finsupp.sub_apply, hT,
    Finsupp.finset_sum_apply]
  have hsum : (∑ d ∈ (Finset.Ico 2 n).attach,
      (if d.1 ∣ n then (channelWeight n d.1 : ℤ) •
        isolatedChannelUnit d.1 else 0) n) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    by_cases hdvd : d.1 ∣ n
    · have hz := isolated_unit_outside d.1 n
        (Or.inr (Finset.mem_Ico.mp d.2).2)
      simp [hdvd, Finsupp.smul_apply, hz]
    · simp [hdvd]
  rw [hsum, sub_zero]
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (N : ℕ) (f : ℕ →₀ ℤ)
    (hzero : f 0 = 0) (hbound : ∀ i : ℕ, N < i → f i = 0) :
    ∃ a : ℕ →₀ ℤ, channelSynthesis a = f := by
  classical
  induction N generalizing f with
  | zero =>
    have hf : f = 0 := by
      ext i
      by_cases hi : i = 0
      · simpa [hi] using hzero
      · exact hbound i (by omega)
    refine ⟨0, ?_⟩
    simp [channelSynthesis, hf]
  | succ N ih =>
    by_cases hN : N = 0
    · subst N
      refine ⟨single 0 (f 1), ?_⟩
      rw [channelSynthesis_single]
      simp only [channelBasisColumn, if_pos rfl]
      ext i
      by_cases hi : i = 1
      · subst i
        simp
      · by_cases hi0 : i = 0
        · subst i
          simp [hzero]
        · have hfi : f i = 0 := hbound i (by omega)
          simp [Finsupp.smul_apply, Finsupp.single_apply, hi, Ne.symm hi, hfi]
    · have hn2 : 2 ≤ N + 1 := by omega
      let f' := f + f (N + 1) • isolatedChannelUnit (N + 1)
      have hf'0 : f' 0 = 0 := by
        simp [f', Finsupp.add_apply, Finsupp.smul_apply, hzero,
          isolated_unit_outside (N + 1) 0 (Or.inl rfl)]
      have hf'bound : ∀ i : ℕ, N < i → f' i = 0 := by
        intro i hi
        by_cases heq : i = N + 1
        · subst i
          simp [f', Finsupp.add_apply, Finsupp.smul_apply,
            isolated_unit_leading hn2, smul_eq_mul]
        · have hNi : N + 1 < i := by omega
          simp [f', Finsupp.add_apply, Finsupp.smul_apply, hbound i hNi,
            isolated_unit_outside (N + 1) i (Or.inr hNi)]
      obtain ⟨a, ha⟩ := ih f' hf'0 hf'bound
      refine ⟨a + single N (-f (N + 1)), ?_⟩
      rw [channelSynthesis_add, channelSynthesis_single, ha]
      simp only [channelBasisColumn, if_neg hN]
      dsimp [f']
      simp only [neg_smul]
      first
        | exact add_neg_cancel_right _ _
        | simp
