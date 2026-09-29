-- Prove2me | Definitions.Def_Logic_AlmostLossless_Scheme
-- name    : Logic_AlmostLossless_Scheme
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:47:01.269459+00:00
-- url     : https://prove2.me/theorems/6ab95080-9912-49ac-b314-3ce1fd104160
-- title:
--   Aether Catalog definitions — Logic_AlmostLossless_Scheme
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AlmostLossless.Scheme`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AlmostLossless/Scheme.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Hashing

/-!
# The Monte-Carlo compressor: hash-and-scan with uniqueness decoding

This file assembles the deliverable of the research thread: an explicit
almost-lossless compression scheme with

* an explicit **failure probability** bound (over the shared random seed and the
  source), see `AlmostLossless.avgFailProb_scanCode_le`;
* an explicit **decoder complexity** figure — the decoder is a single linear
  scan whose cost, counted in hash evaluations, is *exactly* the number of
  candidates it is handed (`AlmostLossless.scanWithCost_cost`), and for the
  bucketed instance the expected number of candidates is at most
  `1 + (|T|-1)/m₁` (`AlmostLossless.expected_bucket_size_le`);
* **no silent corruption**: `AlmostLossless.honest_scanCode` shows the decoder
  is honest *unconditionally* — for every seed, even a catastrophically bad one,
  and for every source word, typical or not.  The uniqueness test built into the
  scan plays the role of a checksum: two candidates means "abort", never a wrong
  answer.

The uniqueness (`ScanState`) decoder is what makes error detection free: the
decoder emits a word only if it is the *unique* candidate matching the received
hash, and the true word is always among the candidates, so an emitted word is
always the true word.
-/

namespace AlmostLossless

open Finset

/-! ## A cost-instrumented uniqueness scan -/

/-- The state of the decoder's linear scan: no candidate yet, exactly one
candidate so far, or at least two (in which case the decoder will abort). -/
inductive ScanState (S : Type*) where
  /-- No matching candidate seen yet. -/
  | empty : ScanState S
  /-- Exactly one matching candidate seen so far. -/
  | unique : S → ScanState S
  /-- At least two matching candidates: the decoder must abort. -/
  | ambiguous : ScanState S
  deriving DecidableEq

variable {S A M : Type*}

/-- One step of the scan: test the candidate, update the uniqueness state. -/
def scanStep (p : S → Bool) (st : ScanState S) (t : S) : ScanState S :=
  if p t then (match st with | .empty => .unique t | _ => .ambiguous) else st

/-- The step specialised to candidates already known to match. -/
def scanStepAll (st : ScanState S) (t : S) : ScanState S :=
  match st with | .empty => .unique t | _ => .ambiguous

/-- The decoder's scan over a candidate list. -/
def scan (p : S → Bool) (L : List S) : ScanState S := L.foldl (scanStep p) .empty

/-- The same scan, instrumented with a counter incremented once per candidate
test (one hash evaluation plus one comparison). -/
def scanWithCost (p : S → Bool) (L : List S) : ScanState S × ℕ :=
  L.foldl (fun st t => (scanStep p st.1 t, st.2 + 1)) (.empty, 0)








/-! ## Scan schemes -/

/-- A **scan scheme**: a typical set `T`, a seeded hash used as the codeword,
and, for each seed and each received codeword, the list of candidates the
decoder scans (in practice produced by a precomputed index of `T`).  The two
axioms say the candidates are typical words and the true word is always a
candidate — these are exactly what makes the decoder honest. -/
structure ScanScheme (S A M : Type*) where
  /-- The typical set the encoder and decoder agree on. -/
  typical : Finset S
  /-- The seeded hash sent as the codeword. -/
  hash : A → S → M
  /-- The candidates the decoder scans on receiving a codeword. -/
  cand : A → M → Finset S
  /-- Candidates are typical words. -/
  cand_subset : ∀ a m, cand a m ⊆ typical
  /-- The true word is always among the candidates. -/
  self_mem_cand : ∀ a s, s ∈ typical → s ∈ cand a (hash a s)

variable [DecidableEq S] [DecidableEq M]

/-- The decoder: scan the candidate list, answer only if the match is unique. -/
noncomputable def ScanScheme.decode (P : ScanScheme S A M) (a : A) (m : M) : Option S :=
  match scan (fun t => decide (P.hash a t = m)) (P.cand a m).toList with
  | .unique t => some t
  | _ => none

/-- The decoder's cost in candidate tests (hash evaluations). -/
def ScanScheme.decodeCost (P : ScanScheme S A M) (a : A) (m : M) : ℕ := (P.cand a m).card


/-- The code induced by a scan scheme with seed `a`.  The encoder sends the hash
of a typical word and an explicit failure flag for an atypical one, so the
codeword alphabet has `|M| + 1` symbols. -/
noncomputable def ScanScheme.code (P : ScanScheme S A M) (a : A) : Code S (Option M) where
  enc s := if s ∈ P.typical then some (P.hash a s) else none
  dec c := c.bind (P.decode a)



/-! ## Failure probability of the Monte-Carlo scheme -/

variable [Fintype S] [Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [Nonempty M]


end AlmostLossless


