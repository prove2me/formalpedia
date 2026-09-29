-- Prove2me | solution 1 for AlmostLossless.card_doubleCollision_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:30:51.87226+00:00
-- url     : https://prove2.me/submissions/348667a5-ed0e-43d0-aadf-26756dc69565

-- Sol generated from Geometry/AlmostLosslessConverse.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Theorems.Thm_AlmostLossless_card_codebooks
/-
# How far beyond the pigeonhole bound can one go?  Converse and tightness

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

Two adversarial questions about the almost-lossless scheme of
`Geometry.AlmostLosslessDecoder`:

1. *How much can the counting bound really be relaxed?*
   `AlmostLossless.converse_card_good_le` — **the ε-relaxed pigeonhole bound**:
   for **any** encoder/decoder pair whatsoever, the set of strings decoded
   correctly has size at most `M`.  So a `(1-ε)`-reliable code for a typical set
   `S` still needs `M ≥ (1-ε)|S|`: relaxation buys a factor `(1-ε)`, no more.

2. *Is the `1/ε` overhead of random hashing an artefact of the union bound?*
   No.  `AlmostLossless.failure_prob_lower_bound` is a **Bonferroni lower bound**
   on the failure probability of uniform random hashing:
   `P[failure] ≥ (|S|-1) / (2M)` once `2(|S|-2) ≤ M`.
   Hence uniform random hashing genuinely needs `M ≳ |S| / ε`, a factor `Θ(1/ε)`
   above the converse — the gap is a property of the *random codebook*, not of
   the analysis.

Supporting combinatorics proved here from scratch:
* `AlmostLossless.card_sum_le_card_biUnion_add_offDiag` — the second Bonferroni
  inequality for an arbitrary finite family of finite sets.
* `AlmostLossless.card_doubleCollision_mul_le` — a two-coordinate refinement of
  the marginal count of `AlmostLosslessCore`: two prescribed collisions have
  probability `1/M²`.
-/

open AlmostLossless

open Finset

/-! ## 1. The ε-relaxed pigeonhole bound (converse) -/



/-! ## 2. Bonferroni: a lower bound for unions of finite sets -/


/-! ## 3. Two prescribed collisions have probability `1/M²` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}


/-! ## 4. The failure probability of random hashing is genuinely `≍ |S|/M` -/

variable {α : Type*} [Fintype α] [DecidableEq α]





open AlmostLossless in
theorem solution{p q r : ι} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    M ^ 2 * ((collisionEvent M p r) ∩ (collisionEvent M q r)).card
      ≤ M ^ Fintype.card ι := by
  classical
  set E := (collisionEvent M p r) ∩ (collisionEvent M q r) with hE
  have hmaps : ∀ z ∈ (E ×ˢ (univ : Finset (Fin M))) ×ˢ (univ : Finset (Fin M)),
      (fun z : ((ι → Fin M) × Fin M) × Fin M =>
        Function.update (Function.update z.1.1 p z.1.2) q z.2) z ∈
        (univ : Finset (ι → Fin M)) := by
    intro z _; exact mem_univ _
  have hinj : Set.InjOn (fun z : ((ι → Fin M) × Fin M) × Fin M =>
      Function.update (Function.update z.1.1 p z.1.2) q z.2)
      ↑((E ×ˢ (univ : Finset (Fin M))) ×ˢ (univ : Finset (Fin M))) := by
    rintro ⟨⟨H, v⟩, w⟩ hz ⟨⟨H', v'⟩, w'⟩ hz' heq
    simp only [coe_product, Set.mem_prod, mem_coe, hE, Finset.mem_inter, collisionEvent,
      mem_filter, mem_univ, true_and] at hz hz'
    obtain ⟨⟨⟨hHp, hHq⟩, -⟩, -⟩ := hz
    obtain ⟨⟨⟨hHp', hHq'⟩, -⟩, -⟩ := hz'
    have hw : w = w' := by
      have := congrArg (fun f => f q) heq
      simpa using this
    have hv : v = v' := by
      have := congrArg (fun f => f p) heq
      simpa [Function.update_apply, hpq] using this
    have hoff : ∀ a, a ≠ p → a ≠ q → H a = H' a := by
      intro a hap haq
      have := congrArg (fun f => f a) heq
      simpa [Function.update_apply, hap, haq] using this
    have hr : H r = H' r := hoff r (Ne.symm hpr) (Ne.symm hqr)
    have hHH : H = H' := by
      funext a
      rcases eq_or_ne a p with hap | hap
      · rw [hap, hHp, hHp', hr]
      · rcases eq_or_ne a q with haq | haq
        · rw [haq, hHq, hHq', hr]
        · exact hoff a hap haq
    simp [hHH, hv, hw]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_univ, card_codebooks] at hcard
  calc M ^ 2 * E.card = E.card * M * M := by ring
    _ ≤ M ^ Fintype.card ι := hcard
