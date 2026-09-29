-- Prove2me | Definitions.Def_Applications_ComputationalEvidence
-- name    : Applications_ComputationalEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:38.310846+00:00
-- url     : https://prove2.me/theorems/199fa6f3-439f-464e-b152-a0a0626e59f9
-- title:
--   Aether Catalog definitions — Applications_ComputationalEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ComputationalEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ComputationalEvidence.lean by skeleton subtraction
import Mathlib

/-! # Computational evidence for finite-state identity

Small explicit Moore machines exercise the behavioural definition on representative cases.
The first machine records parity of `true` inputs.  The second is permanently false.  The
third has redundant physical states but the same observations as the second.  There is no
relevant integer sequence, so an OEIS search is inapplicable.
-/

namespace LifeboxEvidence

/-- Minimal self-contained finite Moore machine used for the checks. -/
structure Machine (Input State Output : Type*) where
  step : State → Input → State
  observe : State → Output

def Machine.runFrom {I S O : Type*} (M : Machine I S O) (s : S) (w : List I) : S :=
  w.foldl M.step s

def TraceEquiv {I S T O : Type*} (M : Machine I S O) (N : Machine I T O)
    (s : S) (t : T) : Prop :=
  ∀ w, M.observe (M.runFrom s w) = N.observe (N.runFrom t w)

/-- A two-state parity observer. -/
def parityPerson : Machine Bool Bool Bool where
  step s a := xor s a
  observe s := s

/-- A one-state observer that always emits false. -/
def silentPerson : Machine Bool Unit Bool where
  step _ _ := ()
  observe _ := false

/-- A physically different two-state implementation whose output is always false. -/
def redundantSilent : Machine Bool Bool Bool where
  step s a := xor s a
  observe _ := false



end LifeboxEvidence


