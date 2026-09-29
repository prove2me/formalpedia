-- Prove2me | solution 1 for AlmostLossless.avg_decodeCost_bucketed_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:28:56.774555+00:00
-- url     : https://prove2.me/submissions/b2fa9385-8c2e-41b7-abd7-a63b8d78f904

-- Sol generated from Logic/AlmostLossless/Instances.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme
import Theorems.Thm_AlmostLossless_avg_collisionCount_le
import Theorems.Thm_AlmostLossless_decodeCost_bucketed_self

/-!
# Instances: linear scan, bucketed scan, and a concrete `ZMod p` compressor

Two instances of `AlmostLossless.ScanScheme`:

* `AlmostLossless.linearScan` — the decoder scans the whole typical set:
  cost exactly `|T|` hash evaluations, deterministic worst case.
* `AlmostLossless.bucketed` — the codeword is a pair (bucket hash, checksum
  hash) and the decoder scans only one bucket, taken from a precomputed index
  of `T`.  Its cost when decoding a typical word `x` is exactly
  `1 + collisionCount`, and the *expected* cost over the random seed is at most
  `1 + (|T|-1)/m₁` (`AlmostLossless.avg_decodeCost_bucketed_le`): the decoder
  becomes essentially constant-time once `m₁ ≳ |T|`, while the transmitted rate
  is `log m₁ + log m₂` bits.

Finally `AlmostLossless.zmod_scheme` packages the whole pipeline over
`(ZMod p)^k` with the inner-product hash family: `k` field symbols are
compressed to *one* symbol plus a failure flag, the decoder is honest for every
seed, its cost is exactly `|T|`, and the average failure probability is at most
`ε + |T|(|T|-1)/p`.  The companion statement
`AlmostLossless.zmod_uniform_hopeless` shows this is no contradiction with the
pigeonhole bound: on the *uniform* source the very same alphabet fails with
probability at least `1 - (p+1)/p^k`.
-/

open AlmostLossless

open Finset

variable {S A M : Type*} [DecidableEq S] [DecidableEq M]

/-! ## The linear-scan scheme -/



/-! ## The bucketed scheme -/


variable {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂]






/-! ## A concrete compressor over `(ZMod p)^k` -/


variable {p k : ℕ} [Fact p.Prime]







open AlmostLossless in
omit [DecidableEq M₂] in
theorem solution[Fintype A₁] [DecidableEq A₁] [Nonempty A₁]
    [Fintype M₁] [Nonempty M₁] (T : Finset S) {h₁ : A₁ → S → M₁} (h₂ : A₂ → S → M₂)
    (hu₁ : TwoUniversal h₁) (a₂ : A₂) {x : S} (hx : x ∈ T) :
    (∑ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
        ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)) / (Fintype.card A₁ : ℚ)
      ≤ 1 + ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) := by
  have hA : (0 : ℚ) < (Fintype.card A₁ : ℚ) := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hterm : ∀ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
      ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)
      = 1 + (collisionCount h₁ T a₁ x : ℚ) := by
    intro a₁
    rw [decodeCost_bucketed_self T h₁ h₂ a₁ a₂ hx]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun a₁ _ => hterm a₁), Finset.sum_add_distrib]
  have havg := avg_collisionCount_le hu₁ T x
  rw [div_le_iff₀ hA] at havg ⊢
  have h1 : ∑ _a₁ : A₁, (1 : ℚ) = (Fintype.card A₁ : ℚ) := by simp
  rw [h1]
  have : ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) * (Fintype.card A₁ : ℚ)
      ≥ ∑ a₁ : A₁, (collisionCount h₁ T a₁ x : ℚ) := havg
  nlinarith [this]
