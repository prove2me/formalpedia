-- Prove2me | solution 1 for EOSWidth.score_digit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:51:12.786866+00:00
-- url     : https://prove2.me/submissions/ecf4c529-57ec-4cd9-aa92-3b2c89facaae

-- Sol generated from Tropical/NeuralNetworks/EOSWidthTropicalSeparation.lean
import Mathlib
import Definitions.Def_Tropical_NeuralNetworks_EOSWidthTropicalSeparation

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







/-- Auxiliary: a tropical sup of a family that is `⊥` off a single index. -/
lemma sup_ite_bot {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (f : ι → WithBot ℝ) :
    (univ.sup fun k => if k = a then f k else ⊥) = f a := by
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro k _
    by_cases h : k = a <;> simp [h]
  · exact le_trans (le_of_eq (by simp))
      (Finset.le_sup (f := fun k => if k = a then f k else ⊥) (mem_univ a))

/-! ## Part 1: which boundary vectors are tropically indistinguishable -/


lemma digit_apply_of_ne {N D : ℕ} (j : Fin D) (i : Fin N) (h : (i : ℕ) ≠ (j : ℕ)) :
    digit N D j i = ⊥ := by
  simp [digit, h]





/-! ## Part 2: max-plus readouts cannot separate a span member -/





/-! ## Part 3: an exclusive dimension buys unbounded, robust separation -/







/-! ## Part 4: zero-padded EOS embeddings -/




open EOSWidth in
theorem solution{N D : ℕ} (hDN : D ≤ N) (w : TVec N) (j : Fin D) :
    score w (digit N D j) = w (Fin.castLE hDN j) := by
  classical
  have key : ∀ i : Fin N,
      (w i + digit N D j i) = if i = Fin.castLE hDN j then w i else ⊥ := by
    intro i
    by_cases hi : i = Fin.castLE hDN j
    · subst hi; simp [digit]
    · have hne : (i : ℕ) ≠ (j : ℕ) := by
        intro h; exact hi (Fin.ext (by simpa using h))
      simp [digit_apply_of_ne j i hne, hi]
  rw [score]
  simp only [key]
  exact sup_ite_bot _ _
