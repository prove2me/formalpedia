-- Prove2me | Definitions.Def_Combinatorics_DNASubsequenceAvoidance
-- name    : Combinatorics_DNASubsequenceAvoidance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:30:29.506715+00:00
-- url     : https://prove2.me/theorems/2a6d6403-f60f-46b9-85d7-f3d6a8e76fd1
-- title:
--   Aether Catalog definitions — Combinatorics_DNASubsequenceAvoidance
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.DNASubsequenceAvoidance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/DNASubsequenceAvoidance.lean by skeleton subtraction
import Mathlib

open Function

namespace DNASubsequenceAvoidance

/-- The `k`-mer beginning at position `i` in a finite word. -/
def selectedKmer {α : Type*} {m k : ℕ} (hkm : k ≤ m) (word : Fin m → α)
    (i : Fin (m - k + 1)) : Fin k → α :=
  fun j => word ⟨i.val + j.val, by omega⟩







end DNASubsequenceAvoidance


