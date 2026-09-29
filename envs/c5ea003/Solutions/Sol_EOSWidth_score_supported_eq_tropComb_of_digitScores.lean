-- Prove2me | solution 1 for EOSWidth.score_supported_eq_tropComb_of_digitScores
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:52:31.071456+00:00
-- url     : https://prove2.me/submissions/08e1aa7e-cd1d-4b74-83ff-acca1b73131a

-- Sol generated from Tropical/NeuralNetworks/EOSWidthTropicalSeparation.lean
import Mathlib
import Definitions.Def_Tropical_NeuralNetworks_EOSWidthTropicalSeparation
import Theorems.Thm_EOSWidth_score_digit

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







/-! ## Part 2: max-plus readouts cannot separate a span member -/





/-! ## Part 3: an exclusive dimension buys unbounded, robust separation -/







/-! ## Part 4: zero-padded EOS embeddings -/




open EOSWidth in
theorem solution{N D : ℕ} (hDN : D ≤ N)
    (x : TVec N) (hx : NoExclusiveDim N D x) (w : TVec N) :
    score w x = univ.sup fun j : Fin D => x (Fin.castLE hDN j) + score w (digit N D j) := by
  classical
  have hright : (univ.sup fun j : Fin D => x (Fin.castLE hDN j) + score w (digit N D j))
      = univ.sup fun j : Fin D => w (Fin.castLE hDN j) + x (Fin.castLE hDN j) := by
    refine Finset.sup_congr rfl ?_
    intro j _
    rw [score_digit hDN w j, add_comm]
  rw [hright, score]
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i _
    by_cases hi : (i : ℕ) < D
    · have hcast : Fin.castLE hDN (⟨(i : ℕ), hi⟩ : Fin D) = i := Fin.ext (by simp)
      calc w i + x i
          = w (Fin.castLE hDN ⟨(i : ℕ), hi⟩) + x (Fin.castLE hDN ⟨(i : ℕ), hi⟩) := by rw [hcast]
        _ ≤ _ := Finset.le_sup (f := fun j : Fin D =>
              w (Fin.castLE hDN j) + x (Fin.castLE hDN j)) (mem_univ _)
    · rw [hx i (by omega)]
      simp
  · refine Finset.sup_le ?_
    intro j _
    exact Finset.le_sup (f := fun i : Fin N => w i + x i) (mem_univ (Fin.castLE hDN j))
