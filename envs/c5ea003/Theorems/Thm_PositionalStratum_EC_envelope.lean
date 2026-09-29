-- Prove2me | Theorems.Thm_PositionalStratum_EC_envelope
-- name    : PositionalStratum.EC_envelope
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:59:17.501806+00:00
-- url     : https://prove2.me/theorems/1c01d833-fe9d-4313-b419-2bde0479911b
-- title:
--   The booked envelope.
-- statement:
--   **The booked envelope.**  Every weight honouring the bookings — head stratum of size
--   `m` inside `M` slots carrying capture mass `P` — has expected scan cost between
--   `P·1 + (1-P)·(m+1)` and `P·m + (1-P)·M`.  These bounds use *only* the bookings, no
--   uniformity assumption.
--
--   ```lean
--   theorem PositionalStratum.EC_envelope{M m : ℕ} {w : ℕ → ℝ} {P : ℝ} (hmM : m ≤ M)
--       (hw : ∀ i, 0 ≤ w i) (hhead : mass (positions m) w = P)
--       (htot : mass (positions M) w = 1) :
--       P * 1 + (1 - P) * ((m : ℝ) + 1) ≤ EC M scanCost w ∧
--         EC M scanCost w ≤ P * m + (1 - P) * M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumEnvelope.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumEnvelope.lean#L46

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

theorem PositionalStratum.EC_envelope{M m : ℕ} {w : ℕ → ℝ} {P : ℝ} (hmM : m ≤ M)
    (hw : ∀ i, 0 ≤ w i) (hhead : mass (positions m) w = P)
    (htot : mass (positions M) w = 1) :
    P * 1 + (1 - P) * ((m : ℝ) + 1) ≤ EC M scanCost w ∧
      EC M scanCost w ≤ P * m + (1 - P) * M := by sorry
