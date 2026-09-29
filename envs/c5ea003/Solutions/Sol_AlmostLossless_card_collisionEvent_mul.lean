-- Prove2me | solution 1 for AlmostLossless.card_collisionEvent_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:12:22.249119+00:00
-- url     : https://prove2.me/submissions/809f8505-4c12-4b26-90ca-1c635f54544f

-- Sol generated from Geometry/AlmostLosslessCore.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Theorems.Thm_AlmostLossless_card_codebooks
/-
# Almost-lossless (Monte-Carlo) compression: the random-hash core

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

This file develops, from scratch, the counting core of Shannon's random-coding
argument in a purely finitary, `Finset`-based form:

* `AlmostLossless.pigeonhole_barrier` — the exact/all-strings barrier:
  an injective encoder into `Fin M` forces `M ≥ |α|`.
* `AlmostLossless.collisionEvent` — the event `H p = H q` inside the finite
  probability space of *all* codebooks `H : ι → Fin M`.
* `AlmostLossless.card_collisionEvent_mul` — the exact marginal count
  `M * |{H | H p = H q}| = M ^ |ι|` for `p ≠ q`, i.e. the collision
  probability of a fixed pair is exactly `1/M`.
* `AlmostLossless.card_multiCollision_mul_le` — the union bound in counting
  form for an arbitrary finite family of pairs.

Everything is stated with integer arithmetic (no measure theory), so all
probability statements are exact counting identities/inequalities.
-/

open AlmostLossless

open Finset

/-! ## 1. The pigeonhole barrier for exact decoding -/



/-! ## 2. The finite probability space of codebooks

The sample space is the (finite) set of *all* functions `H : ι → Fin M`;
"probability" means normalised counting measure, and we keep everything in the
integers by multiplying through by the total number `M ^ |ι|` of codebooks. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}







open AlmostLossless in
theorem solution{p q : ι} (hpq : p ≠ q) :
    M * (collisionEvent M p q).card = M ^ Fintype.card ι := by
  classical
  -- `(H, v) ↦ update H p v` is a bijection from `collisionEvent ×ˢ Fin M` onto all codebooks.
  have hcard : ((collisionEvent M p q) ×ˢ (univ : Finset (Fin M))).card
      = (univ : Finset (ι → Fin M)).card := by
    apply Finset.card_bij (fun z _ => Function.update z.1 p z.2)
    · intro z _; exact mem_univ _
    · rintro ⟨H, v⟩ hH ⟨H', v'⟩ hH' heq
      have hHc : H p = H q := by
        simpa [collisionEvent] using (mem_product.1 hH).1
      have hHc' : H' p = H' q := by
        simpa [collisionEvent] using (mem_product.1 hH').1
      have hv : v = v' := by
        have := congrArg (fun f => f p) heq
        simpa using this
      have hoff : ∀ a, a ≠ p → H a = H' a := by
        intro a ha
        have := congrArg (fun f => f a) heq
        simpa [Function.update_apply, ha] using this
      have hHH : H = H' := by
        funext a
        rcases eq_or_ne a p with ha | ha
        · rw [ha, hHc, hHc', hoff q (Ne.symm hpq)]
        · exact hoff a ha
      exact Prod.ext hHH hv
    · intro H _
      refine ⟨(Function.update H p (H q), H p), ?_, ?_⟩
      · simp only [mem_product, collisionEvent, mem_filter, mem_univ, true_and, and_true]
        rw [Function.update_apply, Function.update_apply, if_pos rfl,
          if_neg (Ne.symm hpq)]
      · funext a
        rcases eq_or_ne a p with ha | ha
        · rw [ha]; simp
        · simp [ha]
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_univ,
    card_codebooks] at hcard
  simpa [mul_comm] using hcard
