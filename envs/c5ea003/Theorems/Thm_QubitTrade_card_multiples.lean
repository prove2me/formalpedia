-- Prove2me | Theorems.Thm_QubitTrade_card_multiples
-- name    : QubitTrade.card_multiples
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:50:52.273527+00:00
-- url     : https://prove2.me/theorems/8b92cb20-a121-4125-ac36-87db0e58287d
-- title:
--   Card multiples
-- statement:
--   Formal statement of `QubitTrade.card_multiples` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem QubitTrade.card_multiples{p : ℕ} (hp : 0 < p) (hd : p ∣ r) :
--       ((Finset.range r).filter (fun x => p ∣ x)).card = r / p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/RecordCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/RecordCount.lean#L47

-- Thm stub generated from Algebra/QubitTrade/RecordCount.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility

/-!
# QUBIT-TRADE IX: how many samples? `log₂ log₂ r` of them

Above the resolution threshold the only obstruction left is `gcd (k, r) > 1`, and
`SampleFungibility.lean` says a record works exactly when its numerators are
jointly coprime to `r`.  Here we *count* the bad records and get the second half
of the resource ledger:

* `QubitTrade.card_bad_records_le` — the number of length-`m` records of
  numerators that fail the joint-coprimality test is at most
  `ω(r) · r^m / 2^m` (stated multiplicatively, in `ℕ`);
* `QubitTrade.exists_good_record` — hence a *successful* record of length `m`
  exists as soon as `ω(r) < 2^m`;
* `QubitTrade.good_record_of_log_log` — and `m = log₂ log₂ r + 1` samples always
  suffice, since `ω(r) ≤ log₂ r`.

Together with `Threshold.lean`: **`2 log₂ r` qubits and `log₂ log₂ r` samples.**
The register size is forced; the sample count is almost free.  That asymmetry is
the precise sense in which qubits and samples are *not* fungible below the
threshold and only mildly fungible above it.
-/

open QubitTrade

open Finset

variable {r m : ℕ}

theorem QubitTrade.card_multiples{p : ℕ} (hp : 0 < p) (hd : p ∣ r) :
    ((Finset.range r).filter (fun x => p ∣ x)).card = r / p := by sorry
