-- Prove2me | Theorems.Thm_PositionalStratum_bookedEC_of_uniform_cells
-- name    : PositionalStratum.bookedEC_of_uniform_cells
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:59:32.22045+00:00
-- url     : https://prove2.me/theorems/6dffdef9-10bd-4feb-8e7d-7c8c3c4987b9
-- title:
--   The booked law is exact on uniform cells.
-- statement:
--   **The booked law is exact on uniform cells.**  If the weight is flat inside the head
--   stratum and flat inside its complement, the expected scan cost is *exactly* the booked
--   value.  Together with `value_universality_fails` this delimits the booked law precisely:
--   an identity on uniform cells, and nothing more off them.
--
--   ```lean
--   theorem PositionalStratum.bookedEC_of_uniform_cells{M m : ℕ} {P : ℝ} {w : ℕ → ℝ} (hm : 0 < m) (hmM : m < M)
--       (hR : ∀ i ∈ positions m, w i = P / m)
--       (hC : ∀ i ∈ positions M \ positions m, w i = (1 - P) / ((M : ℝ) - m)) :
--       EC M scanCost w = bookedEC M m P := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumEnvelope.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumEnvelope.lean#L161

-- Thm stub generated from Applications/PositionalStratumEnvelope.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumEnvelope
import Definitions.Def_Applications_PositionalStratumMeasure
/-
# The booked envelope : the sharp replacement for the failed value law

`Applications.PositionalStratumMeasure.value_universality_fails` shows that the booked
(uniform-within-cell) *value* law is not an upper bound once the weight is allowed to be
non-uniform inside the strata.  This file supplies the guarded version that survives:
a **two-sided envelope** determined by the bookings `(m, M, P)` alone, which is

* valid for *every* weight honouring the bookings (`EC_envelope`),
* **sharp** at both ends (`headWitness_attains_lower`, `tailWitness_attains_upper`), and
* contains the booked value (`bookedEC_mem_envelope`), which is therefore admissible as a
  *reporting* convention but not as a guarantee.

The file also records the F1 reporting convention itself: the positional-stratum law stated
with bookings, `EC = P·Θ_R·centre(R) + (1-P)·Θ_C·centre(C)` (`booked_law_theta_form`) — an
exact identity, never a bare `(μ,P)` closed form.
-/

open PositionalStratum

open Finset

noncomputable section

/-! ## Bounding a stratum's cost contribution by its mass -/




/-! ## The booked envelope -/










/-! ## Exactness at uniform cells : where the booked law is the truth -/

theorem PositionalStratum.bookedEC_of_uniform_cells{M m : ℕ} {P : ℝ} {w : ℕ → ℝ} (hm : 0 < m) (hmM : m < M)
    (hR : ∀ i ∈ positions m, w i = P / m)
    (hC : ∀ i ∈ positions M \ positions m, w i = (1 - P) / ((M : ℝ) - m)) :
    EC M scanCost w = bookedEC M m P := by sorry
