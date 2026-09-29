-- Prove2me | Definitions.Def_Logic_AlmostLossless_Hashing
-- name    : Logic_AlmostLossless_Hashing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:46:14.140262+00:00
-- url     : https://prove2.me/theorems/7597e7ca-ef78-42d3-9701-fed692a67246
-- title:
--   Aether Catalog definitions — Logic_AlmostLossless_Hashing
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AlmostLossless.Hashing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AlmostLossless/Hashing.lean by skeleton subtraction
import Mathlib

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

namespace AlmostLossless

open Finset

variable {S A M : Type*}

/-! ## Two-universality -/

/-- A family of hash functions `h : A → S → M`, indexed by a seed `a : A`, is
**2-universal** when any two distinct source words collide for at most a
`1/|M|` fraction of the seeds.  Written multiplicatively to stay in `ℕ`. -/
def TwoUniversal [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
    (h : A → S → M) : Prop :=
  ∀ x y : S, x ≠ y → #{a | h a x = h a y} * Fintype.card M ≤ Fintype.card A

/-- The stronger, *exact* property: for `x ≠ y` precisely a `1/|M|` fraction of
the seeds collide.  All the classical algebraic families satisfy it. -/
def PairwiseIndependent [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]
    (h : A → S → M) : Prop :=
  ∀ x y : S, x ≠ y → #{a | h a x = h a y} * Fintype.card M = Fintype.card A


/-- The seed `a` is **bad** for the typical set `T`: it confuses two distinct
words of `T`. -/
def CollidesOn [DecidableEq S] [DecidableEq M] (h : A → S → M) (T : Finset S) (a : A) : Prop :=
  ∃ p ∈ T.offDiag, h a p.1 = h a p.2

instance [DecidableEq S] [DecidableEq M] (h : A → S → M) (T : Finset S) (a : A) :
    Decidable (CollidesOn h T a) := by unfold CollidesOn; infer_instance





/-! ## Expected number of false candidates (decoder work) -/

/-- The number of *other* typical words sharing the hash of `x`: exactly the
number of false candidates a bucketed decoder must sift through. -/
def collisionCount [DecidableEq S] [DecidableEq M] (h : A → S → M) (T : Finset S)
    (a : A) (x : S) : ℕ :=
  #{y ∈ T.erase x | h a y = h a x}



/-! ## Products of hash families -/


/-! ## A concrete 2-universal family: inner products over `ZMod p` -/

section Concrete

variable {p k : ℕ} [Fact p.Prime]

/-- The additive homomorphism `a ↦ ⟨a, z⟩` on `(ZMod p)^k`. -/
def dotHom (z : Fin k → ZMod p) : (Fin k → ZMod p) →+ ZMod p where
  toFun a := ∑ i, a i * z i
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

/-- The inner-product hash family: the seed is a vector `a ∈ (ZMod p)^k`, the
hash of a source word `x ∈ (ZMod p)^k` is the single field element `⟨a, x⟩`.
Evaluating it costs exactly `k` multiplications and `k-1` additions. -/
def dotHash (p k : ℕ) : (Fin k → ZMod p) → (Fin k → ZMod p) → ZMod p :=
  fun a x => ∑ i, a i * x i





end Concrete

end AlmostLossless


