-- Prove2me | Definitions.Def_Cryptography_BiOrderSeparation
-- name    : Cryptography_BiOrderSeparation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:11:52.605813+00:00
-- url     : https://prove2.me/theorems/c9956bd6-2005-44cb-bdd2-ed534c4d326a
-- title:
--   Aether Catalog definitions — Cryptography_BiOrderSeparation
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BiOrderSeparation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BiOrderSeparation.lean by skeleton subtraction
import Mathlib

/-!
# Bounded right traces of binary words

This module supplies the finite-word separation facts used by the universal
poset and coherent-composition developments.  A word is a finite binary list.
Its bounded right trace consists of its extensions whose total length is at
most the bound.  Two words that themselves lie under the bound are determined
by these traces.
-/

/-- Finite binary words. -/
abbrev Word := List Bool

/-- The bounded set of right extensions of a word. -/
def rightTraceWord (R : ℕ) (w : Word) : Set Word :=
  {z | z.length ≤ R ∧ ∃ t, z = w ++ t}


