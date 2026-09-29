-- Prove2me | Definitions.Def_Algebra_QubitTrade_RecordCount
-- name    : Algebra_QubitTrade_RecordCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:01:44.575731+00:00
-- url     : https://prove2.me/theorems/f17b1760-4afd-4637-a8b3-5f5b1e7803b5
-- title:
--   Aether Catalog definitions — Algebra_QubitTrade_RecordCount
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QubitTrade.RecordCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QubitTrade/RecordCount.lean by skeleton subtraction
import Mathlib
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

namespace QubitTrade

open Finset

variable {r m : ℕ}

/-- All length-`m` records of numerators below `r`. -/
def allRecords (r m : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m => Finset.range r)

/-- The records that fail the joint-coprimality criterion of `samples_recover`. -/
noncomputable def badRecords (r m : ℕ) : Finset (Fin m → ℕ) :=
  (allRecords r m).filter (fun f => Nat.gcd (recordGcd (List.ofFn f)) r ≠ 1)


/-- Records all of whose entries are divisible by `p`. -/
def multipleRecords (r m p : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m => (Finset.range r).filter (fun x => p ∣ x))








end QubitTrade


