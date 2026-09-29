-- Prove2me | solution 1 for AlmostLossless.card_typical_sq_le_card_mul_sum_decodeCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:17:40.855893+00:00
-- url     : https://prove2.me/submissions/01d5bb55-721b-40d7-a226-3137b1be3e0a

-- Sol generated from Logic/AlmostLossless/Complexity.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme

/-!
# Decoder complexity: an exact expected cost and a universal lower bound

The rate side of almost-lossless compression is settled by `Core`; this file is
about the *time* side, which the research thread identifies as the real
obstacle.

* `AlmostLossless.avg_decodeCost_bucketed_eq` — for a **pairwise independent**
  hash family the expected number of candidate tests performed by the bucketed
  decoder on a typical word is *exactly* `1 + (|T|-1)/m₁`, matching the
  numerical measurements (Section 4 of `ComputationalEvidence.md`) to the digit.
  So the upper bound `avg_decodeCost_bucketed_le` cannot be improved for this
  class of families.

* `AlmostLossless.card_typical_sq_le_card_mul_sum_decodeCost` — a *universal*
  lower bound: for **every** scan scheme and every seed, the total decoding work
  over the typical set is at least `|T|²/|M|` (Cauchy–Schwarz over the buckets),
  and each individual decoding costs at least one test.  Hence no scheme with
  `m` codewords can decode a typical set of size `t` in less than `t/m` expected
  tests: rate and decoding time obey a hyperbolic trade-off.

Together these pin the bucketed decoder to within an additive `1` of optimal.
-/

open AlmostLossless

open Finset

variable {S A M : Type*} [DecidableEq S] [DecidableEq M]

/-! ## Exact expected work for pairwise independent families -/



variable {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂]



/-! ## A universal lower bound on decoder work -/

variable [Fintype M]

omit [DecidableEq S] [Fintype M] in
/-- Every typical word that shares a codeword with `x` is a candidate when `x`'s
codeword is received: the decoder cannot avoid its whole bucket. -/
theorem bucket_subset_cand (P : ScanScheme S A M) (a : A) (x : S) :
    {y ∈ P.typical | P.hash a y = P.hash a x} ⊆ P.cand a (P.hash a x) := by
  intro y hy
  rw [Finset.mem_filter] at hy
  have := P.self_mem_cand a y hy.1
  rwa [hy.2] at this





open AlmostLossless in
omit [DecidableEq S] in
theorem solution(P : ScanScheme S A M) (a : A) :
    (P.typical.card : ℚ) ^ 2
      ≤ (Fintype.card M : ℚ) * ∑ x ∈ P.typical, (P.decodeCost a (P.hash a x) : ℚ) := by
  classical
  set T := P.typical with hT
  set F : M → Finset S := fun m => {y ∈ T | P.hash a y = m} with hF
  have hmaps : ∀ x ∈ T, P.hash a x ∈ (Finset.univ : Finset M) := fun _ _ => Finset.mem_univ _
  -- the bucket of `x` is contained in the candidate set, so bucket sizes lower bound the work
  have hb : ∀ x ∈ T, ((F (P.hash a x)).card : ℚ) ≤ (P.decodeCost a (P.hash a x) : ℚ) := by
    intro x hx
    have := Finset.card_le_card (bucket_subset_cand P a x)
    exact_mod_cast this
  have hsum_b : ∑ x ∈ T, ((F (P.hash a x)).card : ℚ) = ∑ m : M, ((F m).card : ℚ) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => ((F (P.hash a x)).card : ℚ))]
    refine Finset.sum_congr rfl ?_
    intro m _
    have hcongr : ∀ x ∈ {x ∈ T | P.hash a x = m}, ((F (P.hash a x)).card : ℚ)
        = ((F m).card : ℚ) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hx.2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
    have : ({x ∈ T | P.hash a x = m} : Finset S) = F m := rfl
    rw [this, sq]
  have hcard : ∑ m : M, ((F m).card : ℚ) = (T.card : ℚ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun x => P.hash a x) (s := T)
      (t := (Finset.univ : Finset M)) hmaps
    have hq : (T.card : ℚ) = ∑ m : M, (({x ∈ T | P.hash a x = m} : Finset S).card : ℚ) := by
      exact_mod_cast this
    rw [hq]
  have hcheb : (∑ m : M, ((F m).card : ℚ)) ^ 2
      ≤ (Fintype.card M : ℚ) * ∑ m : M, ((F m).card : ℚ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset M))
      (f := fun m => ((F m).card : ℚ))
    simpa [Finset.card_univ] using this
  calc (T.card : ℚ) ^ 2 = (∑ m : M, ((F m).card : ℚ)) ^ 2 := by rw [hcard]
    _ ≤ (Fintype.card M : ℚ) * ∑ m : M, ((F m).card : ℚ) ^ 2 := hcheb
    _ = (Fintype.card M : ℚ) * ∑ x ∈ T, ((F (P.hash a x)).card : ℚ) := by rw [hsum_b]
    _ ≤ (Fintype.card M : ℚ) * ∑ x ∈ T, (P.decodeCost a (P.hash a x) : ℚ) := by
        have hMnn : (0 : ℚ) ≤ (Fintype.card M : ℚ) := by positivity
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) hMnn
