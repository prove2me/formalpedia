-- Prove2me | solution 1 for AlmostLossless.twoUniversal_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:25:14.552108+00:00
-- url     : https://prove2.me/submissions/0016da90-d68c-45d0-a308-22500dd9f5c3

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
theorem solution{A₁ A₂ M₁ M₂ : Type*} [Fintype A₁] [DecidableEq A₁]
    [Fintype A₂] [DecidableEq A₂] [Fintype M₁] [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂]
    {h₁ : A₁ → S → M₁} {h₂ : A₂ → S → M₂} (hu₁ : TwoUniversal h₁) (hu₂ : TwoUniversal h₂) :
    TwoUniversal (fun (a : A₁ × A₂) (x : S) => (h₁ a.1 x, h₂ a.2 x)) := by
  classical
  intro x y hxy
  have hfil : #{a : A₁ × A₂ | (h₁ a.1 x, h₂ a.2 x) = (h₁ a.1 y, h₂ a.2 y)}
      = #{a₁ | h₁ a₁ x = h₁ a₁ y} * #{a₂ | h₂ a₂ x = h₂ a₂ y} := by
    rw [← Finset.card_product]
    apply Finset.card_nbij id
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
        Prod.mk.injEq, Finset.coe_product, Set.mem_prod, id_eq] at ha ⊢
      exact ⟨ha.1, ha.2⟩
    · intro a _ b _ hab; exact hab
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
        Prod.mk.injEq, Finset.coe_product, Set.mem_prod, id_eq] at ha ⊢
      exact ⟨a, ⟨ha.1, ha.2⟩, rfl⟩
  rw [hfil, Fintype.card_prod, Fintype.card_prod]
  calc #{a₁ | h₁ a₁ x = h₁ a₁ y} * #{a₂ | h₂ a₂ x = h₂ a₂ y} * (Fintype.card M₁ * Fintype.card M₂)
      = (#{a₁ | h₁ a₁ x = h₁ a₁ y} * Fintype.card M₁)
          * (#{a₂ | h₂ a₂ x = h₂ a₂ y} * Fintype.card M₂) := by ring
    _ ≤ Fintype.card A₁ * Fintype.card A₂ :=
        Nat.mul_le_mul (hu₁ x y hxy) (hu₂ x y hxy)
