-- Prove2me | Definitions.Def_NumberTheory_RecursiveMixedRadix
-- name    : NumberTheory_RecursiveMixedRadix
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:16.218398+00:00
-- url     : https://prove2.me/theorems/2436b948-68ce-4416-8e68-300c4859140e
-- title:
--   Aether Catalog definitions — NumberTheory_RecursiveMixedRadix
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RecursiveMixedRadix`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RecursiveMixedRadix.lean by skeleton subtraction
import Mathlib

/-!
# Recursive mixed-radix representations

This file isolates the general mixed-radix mechanism behind factoradics and
recursive-base systems.  A radix sequence `r` determines place values
`weight r 0 = 1` and `weight r (k+1) = r k * weight r k`.

The main results prove, constructively and without cardinality arguments, that
valid length-`k` digit strings represent exactly the naturals below
`weight r k`, and do so uniquely.
-/

namespace RecursiveMixedRadix

open Finset

/-- Place values associated to a sequence of radices. -/
def weight (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => r k * weight r k

/-- Value of the first `k` mixed-radix digits. -/
def value (r c : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, c i * weight r i

/-- Every digit lies below its local radix. -/
def Valid (r c : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ i < k, c i < r i

/-- The canonical digit extracted by division and remainder. -/
def digit (r : ℕ → ℕ) (n i : ℕ) : ℕ :=
  (n / weight r i) % r i













end RecursiveMixedRadix


