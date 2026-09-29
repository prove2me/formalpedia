-- Prove2me | solution 1 for AlmostLossless.card_collides_mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:03:24.457755+00:00
-- url     : https://prove2.me/submissions/b2cd0661-9f1d-455e-9448-3dd49a42e270

-- Sol generated from Logic/AlmostLossless/Hashing.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing

/-!
# Two-universal hash families: the derandomised random codebook

Shannon's random-coding argument draws a codebook uniformly at random.  For
*almost-lossless source coding* the only property of the random codebook that
is ever used is that two fixed distinct source words collide with probability
`≤ 1/|M|`.  That is exactly **2-universality**, and it can be achieved by a
family whose seed is `k` field elements and whose evaluation costs `k`
multiplications — an honest "random number generator" with an explicit
complexity figure, as opposed to an exponentially large random codebook.

## Contents

* `AlmostLossless.TwoUniversal` : the defining counting inequality.
* `AlmostLossless.card_collides_mul_card_le` : union bound over the `|T|(|T|-1)`
  ordered pairs of a typical set `T`, giving
  `#{bad seeds} · |M| ≤ |T.offDiag| · |A|`.
* `AlmostLossless.collisionProb_le` : probability form, `P(bad seed) ≤
  |T.offDiag| / |M|`; the Monte-Carlo failure bound of the scheme.
* `AlmostLossless.exists_perfect_seed` : **derandomisation by the probabilistic
  method** — if `|M| > |T|(|T|-1)` then some seed is injective on the whole
  typical set, so the randomness can be removed entirely.
* `AlmostLossless.twoUniversal_dotHash` : a concrete instance, the inner-product
  family `h_a(x) = ∑ a i * x i` over `ZMod p`, proved 2-universal from the
  fact that a nonzero linear functional on `(ZMod p)^k` has all fibres of the
  same size.
-/

open AlmostLossless

open Finset

variable {S A M : Type*}

/-! ## Two-universality -/










/-! ## Expected number of false candidates (decoder work) -/




/-! ## Products of hash families -/


/-! ## A concrete 2-universal family: inner products over `ZMod p` -/


variable {p k : ℕ} [Fact p.Prime]









open AlmostLossless in
theorem solution[Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
    [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S) :
    #{a | CollidesOn h T a} * Fintype.card M ≤ T.offDiag.card * Fintype.card A := by
  classical
  have hsub : ({a | CollidesOn h T a} : Finset A) ⊆
      T.offDiag.biUnion (fun p => ({a | h a p.1 = h a p.2} : Finset A)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨p, hp, hcol⟩ := ha
    exact Finset.mem_biUnion.2 ⟨p, hp, by simp [hcol]⟩
  have h1 : #{a | CollidesOn h T a} ≤ ∑ p ∈ T.offDiag, #{a | h a p.1 = h a p.2} :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  calc #{a | CollidesOn h T a} * Fintype.card M
      ≤ (∑ p ∈ T.offDiag, #{a | h a p.1 = h a p.2}) * Fintype.card M :=
        Nat.mul_le_mul_right _ h1
    _ = ∑ p ∈ T.offDiag, #{a | h a p.1 = h a p.2} * Fintype.card M := by
        rw [Finset.sum_mul]
    _ ≤ ∑ _p ∈ T.offDiag, Fintype.card A := by
        refine Finset.sum_le_sum ?_
        intro p hp
        exact hu p.1 p.2 (Finset.mem_offDiag.1 hp).2.2
    _ = T.offDiag.card * Fintype.card A := by
        rw [Finset.sum_const, smul_eq_mul]
