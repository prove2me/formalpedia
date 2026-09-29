-- Prove2me | Definitions.Def_Cryptography_GameTheory_SchnorrTranscripts
-- name    : Cryptography_GameTheory_SchnorrTranscripts
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:35.025101+00:00
-- url     : https://prove2.me/theorems/bfccb533-6e36-47a7-af5e-b6ceaeb52565
-- title:
--   Aether Catalog definitions — Cryptography_GameTheory_SchnorrTranscripts
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.GameTheory.SchnorrTranscripts`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/GameTheory/SchnorrTranscripts.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Schnorr transcripts and the forking extractor

Basic data for the algebraic analysis of Schnorr witness extraction: a
transcript `(a, c, z)`, the verification predicate `z * gen = a + c * pub`, a
*forked* pair of transcripts sharing the commitment `a` but with distinct
challenges, and the extractor `(z₁ - z₂) * (c₁ - c₂)⁻¹`.

These definitions are used by `Cryptography.GameTheory.Extraction`.
-/

variable {q : ℕ}

/-- A Schnorr transcript: commitment `a`, challenge `c`, response `z`. -/
structure SchnorrTranscript (q : ℕ) where
  /-- The commitment. -/
  a : ZMod q
  /-- The challenge. -/
  c : ZMod q
  /-- The response. -/
  z : ZMod q

/-- The Schnorr verification equation `z * gen = a + c * pub`. -/
def schnorrVerifies (gen pub : ZMod q) (T : SchnorrTranscript q) : Prop :=
  T.z * gen = T.a + T.c * pub


