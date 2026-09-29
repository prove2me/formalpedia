-- Prove2me | Definitions.Def_Novelty_Betti
-- name    : Novelty_Betti
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:07:32.510556+00:00
-- url     : https://prove2.me/theorems/7ebceb12-1e23-47dc-9081-56d6c5eed524
-- title:
--   Aether Catalog definitions — Novelty_Betti
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Betti`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Betti.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ErrorMitigation

/-!
# Betti-count recovery from noisy barcodes

Given a finite barcode `B : Fin n → Bar`, the *Betti count at threshold `τ`* is the
number of bars whose persistence strictly exceeds `τ`.  We prove:

* `betti_antitone`: the Betti count is antitone in the threshold.
* `betti_recovered`: if every noisy persistence is within `ε` of the true persistence,
  every true persistence is separated from `τ` by a margin `m`, and `2 * ε < m`, then
  the noisy Betti count equals the true Betti count.

The recovery proof is non-circular: it flows from the pointwise lemma
`threshold_iff_of_noise_margin` (proved in `ErrorMitigation.lean`) to a pointwise
threshold equivalence, then to equality of the filtered `Finset`s, then to equality of
their cardinalities.  `ErrorMitigation.lean` does not import this file.
-/

namespace Catalog.Novelty.QuantumTopoMitigation

open Finset

/-- The Betti count of a finite barcode `B` at threshold `τ`: the number of bars whose
persistence is strictly greater than `τ`. -/
noncomputable def bettiCount (τ : ℝ) {n : ℕ} (B : Fin n → Bar) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => τ < persistence (B i)).card



end Catalog.Novelty.QuantumTopoMitigation


