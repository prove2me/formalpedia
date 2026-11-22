-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:06:19.747868+00:00
-- url     : https://prove2.me/submissions/148f68cf-b4cd-4866-83a3-c80cdb351855

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_010

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge -/
section


/-!
# Literal canonical residual for the selector-to-tangent handoff

The canonical Saias reduction currently stops at a selector continuation: it
does not yet construct the pre-tangent rounded selector.  This file removes
the *generic residual* ambiguity without asserting that missing construction.

For a supplied selector `x`, the residual coordinate at a medium prime is
defined literally as

`valuation(selectorTailTarget) - valuation(x)`.

The two remaining selector inputs are named explicitly.  The post-rounding
prime-band balance says that these coordinates sum to zero, while prime-band
support says that the selector already has the target valuation at every
prime outside the band.  Neither fact follows merely from
`roughCanonicalRawRowQuotaError`: that quantity is a complete-rough row quota
error, not a prime-coordinate valuation identity.

From those inputs, the finite prime residual has zero total mass and its
positive star split requests have exactly the valuation deficit required by
`tangentUpdate_valuation_eq_target`.  The final theorem also retains the
all-row integrality input verbatim.  It does not claim that clean common
multipliers, feasibility of the tangent update, or the selector itself have
already been constructed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal selector deficit and its finite prime domain -/















/-! ## Prime-label geometry and exact residual algebra -/







/-- At a non-prime coordinate, both the target and every candidate
factorization vanish. -/
theorem bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) {q : ℕ}
    (hq : ¬q.Prime) :
    bankPaperCanonicalSelectorValuationDeficit
      R certificate fixed candidates x q = 0 := by
  simp [bankPaperCanonicalSelectorValuationDeficit,
    Nat.factorization_eq_zero_of_not_prime _ hq]







/-! ## Instantiation of the star split-request boundary -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightOrdinaryLogLedgerConnector -/
section


/-!
# Exact post-height ordinary-log ledger

The post-height baseline realizes the paper's ordinary logarithm exactly.
This file connects that finite moment to the residual selector target.

There are two logically separate ingredients.

* The target/frozen charge ledger identifies the logarithm left for the
  fractional selector after the fixed factors and the state-zero bank.
* Primewise source support says that every valuation deficit outside
  `W < p <= y` is already zero.

Together with the exact post-height moment these imply that the
`tPrime`-weighted initial residual is zero.  No ordinary-log compatibility,
weighted-residual identity, or target envelope is assumed as an input.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## A finite factorization support for a selector -/



/-- Expand the target logarithm on the common finite selector support. -/
theorem bankPaperCanonical_log_target_eq_sum_factorization_on_selectorLogSupport
    (target : Nat) (candidates : Finset Nat) :
    Real.log (target : Real) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (target.factorization p : Real) * Real.log (p : Real) := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  change
    (∑ p ∈ target.factorization.support,
        (target.factorization p : Real) * Real.log (p : Real)) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (target.factorization p : Real) * Real.log (p : Real)
  apply Finset.sum_subset
  · exact Finset.subset_union_left
  · intro p _hp hpNotSupport
    have hpZero : target.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNotSupport
    simp [hpZero]

/-- Expand one candidate logarithm on the same common finite support. -/
theorem bankPaperCanonical_log_candidate_eq_sum_factorization_on_selectorLogSupport
    (target : Nat) (candidates : Finset Nat)
    {a : Nat} (ha : a ∈ candidates) :
    Real.log (a : Real) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (a.factorization p : Real) * Real.log (p : Real) := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  change
    (∑ p ∈ a.factorization.support,
        (a.factorization p : Real) * Real.log (p : Real)) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (a.factorization p : Real) * Real.log (p : Real)
  apply Finset.sum_subset
  · intro p hp
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨a, ha, hp⟩)
  · intro p _hp hpNotSupport
    have hpZero : a.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNotSupport
    simp [hpZero]

/-! ## Ordinary logarithm equals the logarithmically weighted deficit -/

/-- Once the selector deficit is supported on the medium-prime band, its
ordinary logarithmic defect is exactly the `log p`-weighted band deficit.

This is the finite unique-factorization calculation underlying the paper's
display `sum_p r_p log p = 0`. -/
theorem bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates selector) :
    Real.log (certificate.selectorTailTarget R fixed : Real) -
        ∑ a ∈ candidates, selector a * Real.log (a : Real) =
      ∑ p ∈ primeBand n W,
        bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector p *
          Real.log (p : Real) := by
  classical
  let target := certificate.selectorTailTarget R fixed
  let support :=
    bankPaperCanonicalSelectorLogSupport target candidates ∪ primeBand n W
  have htarget :
      Real.log (target : Real) =
        ∑ p ∈ support,
          (target.factorization p : Real) * Real.log (p : Real) := by
    rw [
      bankPaperCanonical_log_target_eq_sum_factorization_on_selectorLogSupport
        target candidates]
    apply Finset.sum_subset
    · exact Finset.subset_union_left
    · intro p _hp hpNot
      have hpZero : target.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hpFactor
        apply hpNot
        exact Finset.mem_union_left _ hpFactor
      simp [hpZero]
  have hcandidate (a : Nat) (ha : a ∈ candidates) :
      Real.log (a : Real) =
        ∑ p ∈ support,
          (a.factorization p : Real) * Real.log (p : Real) := by
    rw [
      bankPaperCanonical_log_candidate_eq_sum_factorization_on_selectorLogSupport
        target candidates ha]
    apply Finset.sum_subset
    · exact Finset.subset_union_left
    · intro p _hp hpNot
      have hpZero : a.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hpFactor
        apply hpNot
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨a, ha, hpFactor⟩)
      simp [hpZero]
  have hselectorSwap :
      (∑ a ∈ candidates,
          selector a *
            ∑ p ∈ support,
              (a.factorization p : Real) * Real.log (p : Real)) =
        ∑ p ∈ support,
          (∑ a ∈ candidates,
              selector a * (a.factorization p : Real)) *
            Real.log (p : Real) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  have hfull :
      Real.log (target : Real) -
          ∑ a ∈ candidates, selector a * Real.log (a : Real) =
        ∑ p ∈ support,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real) := by
    have hselectorLog :
        (∑ a ∈ candidates, selector a * Real.log (a : Real)) =
          ∑ a ∈ candidates,
            selector a *
              ∑ p ∈ support,
                (a.factorization p : Real) * Real.log (p : Real) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hcandidate a ha]
    rw [htarget]
    rw [hselectorLog]
    rw [hselectorSwap, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    unfold bankPaperCanonicalSelectorValuationDeficit
    dsimp only [target]
    ring
  have hbandSubset : primeBand n W ⊆ support :=
    Finset.subset_union_right
  have houtside :
      (∑ p ∈ support,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real)) =
        ∑ p ∈ primeBand n W,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real) := by
    symm
    apply Finset.sum_subset hbandSubset
    intro p _hpSupport hpNotBand
    have hpZero :
        bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector p = 0 := by
      by_cases hpPrime : p.Prime
      · exact hsupport p hpPrime hpNotBand
      · exact
          bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
            R certificate fixed candidates selector hpPrime
    simp [hpZero]
  simpa only [target] using hfull.trans houtside





/-! ## Exact active/frozen logarithmic decomposition -/





/-! ## The exact selector-tail charge -/





/-! ## The fresh post-height seed realizes `logY - Lambda0` -/



/-! ## Complete post-height selector ledger -/









end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real} {depth n W : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization n
      (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
  (certificate : Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth n left right changed)
  (fixed candidates : Finset.{0} Nat) (selector : Nat → Real),
  @Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand c depth n W left right changed R
      certificate fixed candidates selector →
    @Eq.{1} Real
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (Real.log
          (@Nat.cast.{0} Real Real.instNatCast
            (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget c depth n left right changed
              certificate R fixed)))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid candidates fun (a : Nat) =>
          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (selector a)
            (Real.log (@Nat.cast.{0} Real Real.instNatCast a))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Erdos390.Full.ArithmeticModel.primeBand n W) fun (p : Nat) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Erdos390.WholePaper.bankPaperCanonicalSelectorValuationDeficit c depth n left right changed R certificate
            fixed candidates selector p)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast p))) := by
  exact @Erdos390.WholePaper.bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
