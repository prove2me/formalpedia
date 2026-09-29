-- Prove2me | Definitions.Def_Tropical_NeuralNetworks_EOSWidthTropicalSeparation
-- name    : Tropical_NeuralNetworks_EOSWidthTropicalSeparation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:13.969872+00:00
-- url     : https://prove2.me/theorems/21521e88-9ce4-42e9-9006-c3957ab58102
-- title:
--   Aether Catalog definitions — Tropical_NeuralNetworks_EOSWidthTropicalSeparation
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.NeuralNetworks.EOSWidthTropicalSeparation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/NeuralNetworks/EOSWidthTropicalSeparation.lean by skeleton subtraction
import Mathlib

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

namespace EOSWidth

open Finset

/-- Max-plus vectors of width `N`: coordinates in `WithBot ℝ`, where `⊥` plays
the role of the tropical zero `-∞` ("this dimension is not used"). -/
abbrev TVec (N : ℕ) := Fin N → WithBot ℝ

/-- The one-hot tropical digit atom for digit `j`: tropical one (`0`) on
coordinate `j`, tropical zero (`⊥`) elsewhere.  There are `D` digit atoms,
living in the ambient width `N`. -/
def digit (N D : ℕ) (j : Fin D) : TVec N := fun i => if (i : ℕ) = (j : ℕ) then 0 else ⊥

/-- A tropical (max-plus) linear combination `⨁ₖ λₖ ⊙ aₖ` of a finite family of
vectors. -/
def tropComb {N K : ℕ} (a : Fin K → TVec N) (l : Fin K → WithBot ℝ) : TVec N :=
  fun i => univ.sup fun k => l k + a k i

/-- The tropical span of the `D` digit atoms inside width `N`. -/
def InDigitSpan (N D : ℕ) (x : TVec N) : Prop :=
  ∃ l : Fin D → WithBot ℝ, x = tropComb (digit N D) l

/-- `x` uses no dimension beyond the digit block `{0,…,D-1}`. -/
def NoExclusiveDim (N D : ℕ) (x : TVec N) : Prop := ∀ i : Fin N, D ≤ (i : ℕ) → x i = ⊥

/-- `p` is a dimension owned exclusively by `x` (outside the digit block). -/
def ExclusiveDim (N D : ℕ) (x : TVec N) (p : Fin N) : Prop := D ≤ (p : ℕ) ∧ x p ≠ ⊥


/-! ## Part 1: which boundary vectors are tropically indistinguishable -/







/-! ## Part 2: max-plus readouts cannot separate a span member -/

/-- A max-plus readout (tropical linear functional) with weights `w`. -/
def score {N : ℕ} (w x : TVec N) : WithBot ℝ := univ.sup fun i => w i + x i




/-! ## Part 3: an exclusive dimension buys unbounded, robust separation -/

/-- The readout that listens only to coordinate `p` with gain `g`. -/
def probe {N : ℕ} (p : Fin N) (g : ℝ) : TVec N := fun i => if i = p then (g : WithBot ℝ) else ⊥






/-! ## Part 4: zero-padded EOS embeddings -/

/-- The zero-padded EOS embedding of width `E` inside ambient width `N`:
tropical one on the first `E` coordinates, tropical zero beyond. -/
def eosVec (N E : ℕ) : TVec N := fun i => if (i : ℕ) < E then 0 else ⊥


end EOSWidth


