-- Prove2me | Definitions.Def_Algebra_SauerShelah
-- name    : Algebra_SauerShelah
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:48:13.747194+00:00
-- url     : https://prove2.me/theorems/b3b65bbc-0d17-409d-8790-2eb273dff9df
-- title:
--   Aether Catalog definitions — Algebra_SauerShelah
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.SauerShelah`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/SauerShelah.lean by skeleton subtraction
import Mathlib

open Fin

/-! # CatalogBuild.Algebra.SauerShelah

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17
-/


/-- A family `F` of sets **shatters** a set `A` if every subset of `A` arises as
`A ∩ S` for some `S ∈ F`. -/
def Shatters {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) : Prop :=
  ∀ B ⊆ A, ∃ S ∈ F, A ∩ S = B




/-- Drop the last coordinate: keep `i : Fin n` iff `castSucc i ∈ S`. -/
def proj {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.castSucc ∈ S




/-- Embed via `castSucc`. -/
def embed {n : ℕ} (T : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  T.image Fin.castSucc

-- ================================================================
--  Basic proj / embed API
-- ================================================================


