-- Prove2me | solution 1 for AlmostLossless.avgFailProb_scanCode_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:12:25.892791+00:00
-- url     : https://prove2.me/submissions/ef5b60db-e375-47b6-90b2-eec01698c6de

-- Sol generated from Logic/AlmostLossless/Scheme.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Scheme
import Theorems.Thm_AlmostLossless_collisionProb_le
import Theorems.Thm_AlmostLossless_correct_scanCode
import Theorems.Thm_AlmostLossless_failProb_le_of_correct_on
import Theorems.Thm_AlmostLossless_failProb_le_one
import Theorems.Thm_AlmostLossless_injOn_of_not_collidesOn

/-!
# The Monte-Carlo compressor: hash-and-scan with uniqueness decoding

This file assembles the deliverable of the research thread: an explicit
almost-lossless compression scheme with

* an explicit **failure probability** bound (over the shared random seed and the
  source), see `AlmostLossless.avgFailProb_scanCode_le`;
* an explicit **decoder complexity** figure — the decoder is a single linear
  scan whose cost, counted in hash evaluations, is *exactly* the number of
  candidates it is handed (`AlmostLossless.scanWithCost_cost`), and for the
  bucketed instance the expected number of candidates is at most
  `1 + (|T|-1)/m₁` (`AlmostLossless.expected_bucket_size_le`);
* **no silent corruption**: `AlmostLossless.honest_scanCode` shows the decoder
  is honest *unconditionally* — for every seed, even a catastrophically bad one,
  and for every source word, typical or not.  The uniqueness test built into the
  scan plays the role of a checksum: two candidates means "abort", never a wrong
  answer.

The uniqueness (`ScanState`) decoder is what makes error detection free: the
decoder emits a word only if it is the *unique* candidate matching the received
hash, and the true word is always among the candidates, so an emitted word is
always the true word.
-/

open AlmostLossless

open Finset

/-! ## A cost-instrumented uniqueness scan -/


variable {S A M : Type*}












/-! ## Scan schemes -/


variable [DecidableEq S] [DecidableEq M]







/-! ## Failure probability of the Monte-Carlo scheme -/

variable [Fintype S] [Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [Nonempty M]



open AlmostLossless in
theorem solution(μ : Source S) (P : ScanScheme S A M)
    (hu : TwoUniversal P.hash) (ε : ℚ) (hε : 0 ≤ ε) (hT : 1 - ε ≤ μ.prob P.typical) :
    avgFailProb μ (fun a => P.code a)
      ≤ ε + (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ) := by
  classical
  have hA : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast Fintype.card_pos (α := A)
  -- split the seeds into good ones and bad ones
  set B : Finset A := {a | CollidesOn P.hash P.typical a} with hB
  have hgood : ∀ a ∈ Bᶜ, failProb μ (P.code a) ≤ ε := by
    intro a ha
    have hna : ¬ CollidesOn P.hash P.typical a := by
      simpa [hB, Finset.mem_compl] using ha
    exact failProb_le_of_correct_on μ _ P.typical
      (fun s hs => correct_scanCode P a (injOn_of_not_collidesOn hna) hs) ε hT
  have hbad : ∀ a ∈ B, failProb μ (P.code a) ≤ 1 := fun a _ => failProb_le_one μ _
  have hsum : ∑ a, failProb μ (P.code a) ≤ (Fintype.card A : ℚ) * ε + (B.card : ℚ) := by
    have hsplit : ∑ a, failProb μ (P.code a)
        = ∑ a ∈ B, failProb μ (P.code a) + ∑ a ∈ Bᶜ, failProb μ (P.code a) := by
      rw [Finset.sum_add_sum_compl]
    rw [hsplit]
    have h1 : ∑ a ∈ B, failProb μ (P.code a) ≤ (B.card : ℚ) := by
      calc ∑ a ∈ B, failProb μ (P.code a) ≤ ∑ _a ∈ B, (1 : ℚ) :=
            Finset.sum_le_sum hbad
        _ = (B.card : ℚ) := by simp
    have h2 : ∑ a ∈ Bᶜ, failProb μ (P.code a) ≤ (Fintype.card A : ℚ) * ε := by
      calc ∑ a ∈ Bᶜ, failProb μ (P.code a) ≤ ∑ _a ∈ Bᶜ, ε := Finset.sum_le_sum hgood
        _ = (Bᶜ.card : ℚ) * ε := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card A : ℚ) * ε := by
            have : (Bᶜ.card : ℚ) ≤ (Fintype.card A : ℚ) := by
              exact_mod_cast Finset.card_le_univ Bᶜ
            exact mul_le_mul_of_nonneg_right this hε
    linarith
  have hcoll : (B.card : ℚ) / (Fintype.card A : ℚ)
      ≤ (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ) := collisionProb_le hu _
  rw [avgFailProb, div_le_iff₀ hA]
  have hstep : (B.card : ℚ) ≤ (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ)
      * (Fintype.card A : ℚ) := by
    rw [div_le_iff₀ hA] at hcoll
    linarith
  calc ∑ a, failProb μ (P.code a) ≤ (Fintype.card A : ℚ) * ε + (B.card : ℚ) := hsum
    _ ≤ (Fintype.card A : ℚ) * ε
        + (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ) * (Fintype.card A : ℚ) := by
          linarith
    _ = (ε + (P.typical.offDiag.card : ℚ) / (Fintype.card M : ℚ)) * (Fintype.card A : ℚ) := by
          ring
