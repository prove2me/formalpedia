-- Prove2me | solution 1 for EOSWidth.eosVec_inDigitSpan_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:51:11.91792+00:00
-- url     : https://prove2.me/submissions/69ac3c9f-a5c3-41eb-aaef-b2c92987966a

-- Sol generated from Tropical/NeuralNetworks/EOSWidthTropicalSeparation.lean
import Mathlib
import Definitions.Def_Tropical_NeuralNetworks_EOSWidthTropicalSeparation
import Theorems.Thm_EOSWidth_tropComb_digit_apply_lt

/-!
# Tropical separation theory of boundary tokens ("EOS width")

This file gives a max-plus (tropical) model of the empirical phenomenon
recorded in round NET-26 (*EOS-WIDTH-DISTRIBUTION-SHIFT*): a boundary
("end-of-sequence") input of width `E` cures a recurrent carry-wall failure
robustly exactly when it owns dimensions that no digit token uses, and is
seed-fragile when its width sits inside the digit subspace (`E ≤ D`).

The formal claim isolated here is that the *control variable is
representational distinctness, not width*:

* `eos_mem_digitSpan_iff` — a boundary vector lies in the tropical (max-plus)
  span of the one-hot digit atoms **iff** it has no exclusive dimension.
* `score_supported_eq_tropComb_of_digitScores` — if it has no exclusive
  dimension, then for **every** max-plus readout `w` the boundary response is a
  fixed tropical combination of the digit responses: the readout cannot tell the
  boundary from a digit step except through digit-controlled quantities.
* `margin_le_of_no_exclusive_dim` — consequently the boundary-vs-digit margin is
  bounded by the boundary's own coefficients, uniformly in `w`.
* `exclusive_dim_unbounded_margin` — with one exclusive dimension the margin
  becomes unbounded (indeed the digit responses can be driven to the tropical
  zero `⊥`), and
* `exclusive_dim_margin_robust` — the separation survives arbitrary bounded
  perturbations of the readout weights.

Everything is stated over the max-plus semiring on `WithBot ℝ`
(`⊕ = max = ⊔`, `⊙ = +`, tropical zero `⊥ = -∞`, tropical one `0`).
-/

open EOSWidth

open Finset








/-! ## Part 1: which boundary vectors are tropically indistinguishable -/


lemma digit_apply_of_ne {N D : ℕ} (j : Fin D) (i : Fin N) (h : (i : ℕ) ≠ (j : ℕ)) :
    digit N D j i = ⊥ := by
  simp [digit, h]


/-- Evaluating a tropical combination of digit atoms outside the digit block
gives the tropical zero: the digit atoms simply do not reach there. -/
lemma tropComb_digit_apply_ge {N D : ℕ} (l : Fin D → WithBot ℝ) (i : Fin N)
    (hi : D ≤ (i : ℕ)) :
    tropComb (digit N D) l i = ⊥ := by
  have hb : ∀ k : Fin D, (l k + digit N D k i) = ⊥ := by
    intro k
    have hne : (i : ℕ) ≠ (k : ℕ) := by have := k.isLt; omega
    simp [digit_apply_of_ne k i hne]
  simp [tropComb, hb]

/-- **Representational distinctness is exactly the absence of exclusive
dimensions.**  A boundary vector lies in the tropical span of the digit atoms
iff it uses no dimension outside the digit block. -/
theorem eos_mem_digitSpan_iff {N D : ℕ} (hDN : D ≤ N) (x : TVec N) :
    InDigitSpan N D x ↔ NoExclusiveDim N D x := by
  constructor
  · rintro ⟨l, rfl⟩ i hi
    exact tropComb_digit_apply_ge l i hi
  · intro hx
    refine ⟨fun j => x (Fin.castLE hDN j), ?_⟩
    funext i
    by_cases hi : (i : ℕ) < D
    · have hcast : Fin.castLE hDN (⟨(i : ℕ), hi⟩ : Fin D) = i := Fin.ext (by simp)
      rw [tropComb_digit_apply_lt _ i hi, hcast]
    · rw [tropComb_digit_apply_ge _ i (by omega), hx i (by omega)]


/-! ## Part 2: max-plus readouts cannot separate a span member -/





/-! ## Part 3: an exclusive dimension buys unbounded, robust separation -/







/-! ## Part 4: zero-padded EOS embeddings -/




open EOSWidth in
theorem solution{N D E : ℕ} (hDN : D < N) :
    InDigitSpan N D (eosVec N E) ↔ E ≤ D := by
  rw [eos_mem_digitSpan_iff (le_of_lt hDN)]
  constructor
  · intro h
    by_contra hED
    have hp : D < E := by omega
    have hval := h ⟨D, hDN⟩ (by simp)
    simp only [eosVec, if_pos hp] at hval
    exact absurd hval (by simp)
  · intro hED i hi
    simp only [eosVec]
    rw [if_neg (by omega)]
