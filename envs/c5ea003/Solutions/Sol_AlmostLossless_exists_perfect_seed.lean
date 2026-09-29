-- Prove2me | solution 1 for AlmostLossless.exists_perfect_seed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:21:00.841083+00:00
-- url     : https://prove2.me/submissions/f7d49847-f176-483e-bf3b-f1b753fb74de

-- Sol generated from Logic/AlmostLossless/Hashing.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Theorems.Thm_AlmostLossless_card_collides_mul_card_le
import Theorems.Thm_AlmostLossless_injOn_of_not_collidesOn

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
theorem solution[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [DecidableEq M]
    [Nonempty M] [DecidableEq S] {h : A → S → M} (hu : TwoUniversal h) (T : Finset S)
    (hlt : T.offDiag.card < Fintype.card M) :
    ∃ a : A, ∀ x ∈ T, ∀ y ∈ T, h a x = h a y → x = y := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : ∀ a : A, CollidesOn h T a := by
    intro a
    by_contra hna
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hcon a
    exact hne (injOn_of_not_collidesOn hna x hx y hy hxy)
  have hcard : #{a | CollidesOn h T a} = Fintype.card A := by
    rw [Finset.filter_true_of_mem (fun a _ => hall a), Finset.card_univ]
  have hb := card_collides_mul_card_le hu T
  rw [hcard] at hb
  have hApos : 0 < Fintype.card A := Fintype.card_pos
  have : Fintype.card A * Fintype.card M < Fintype.card A * Fintype.card M := by
    calc Fintype.card A * Fintype.card M ≤ T.offDiag.card * Fintype.card A := hb
      _ < Fintype.card M * Fintype.card A := by
          exact Nat.mul_lt_mul_of_lt_of_le hlt (le_refl _) hApos
      _ = Fintype.card A * Fintype.card M := Nat.mul_comm _ _
  exact lt_irrefl _ this
