-- Prove2me | Definitions.Def_Applications_PositionalStratumEnvelope
-- name    : Applications_PositionalStratumEnvelope
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:26.215184+00:00
-- url     : https://prove2.me/theorems/aa57c795-544d-4c11-9463-cb98839b82b5
-- title:
--   Aether Catalog definitions — Applications_PositionalStratumEnvelope
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PositionalStratumEnvelope`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PositionalStratumEnvelope.lean by skeleton subtraction
import Mathlib
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

namespace PositionalStratum

open Finset

noncomputable section

/-! ## Bounding a stratum's cost contribution by its mass -/




/-! ## The booked envelope -/



/-- The extremal tail witness: all captured mass at the *last* slot of the stratum and all
escaping mass at the last slot overall. -/
def tailWitness (m M : ℕ) (P : ℝ) : ℕ → ℝ :=
  fun i => if i = m then P else if i = M then 1 - P else 0







/-! ## Exactness at uniform cells : where the booked law is the truth -/


/-! ## The F1 reporting convention : the law with bookings -/


end

end PositionalStratum


