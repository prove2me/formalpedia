-- Prove2me | Definitions.Def_Kourovka_Covers_ComputableCoverData
-- name    : Kourovka_Covers_ComputableCoverData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:46:43.600933+00:00
-- url     : https://prove2.me/theorems/4f0c5422-40d9-4f0d-add9-88bb87679e80
-- title:
--   Computable Cover Data
-- statement:
--   Definitions and structural lemmas for Computable Cover Data, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverData.lean

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
abbrev PolynomialCode := Bool × List (List ℤ × ℤ)
abbrev DatumCode := (ℕ × ℕ) × (List (List ℕ) × List PolynomialCode)
def dimension (data : DatumCode) : ℕ := data.1.1 + 1
def alphabet (data : DatumCode) : ℕ := data.1.2 + 1
def decodePolynomial (k : ℕ) (p : PolynomialCode) : FiniteCover.Polynomial k :=
  (p.1, p.2.map fun term => ((fun i : Fin k => term.1.getD i 0), term.2))
def decode (data : DatumCode) : FiniteCover.Datum (dimension data) (alphabet data) where
  designated i j := ⟨((data.2.1.getD i []).getD j 0) % alphabet data, Nat.mod_lt _ (Nat.succ_pos _)⟩
  polynomials := data.2.2.map (decodePolynomial (dimension data))
def encode {k a : ℕ} (data : FiniteCover.Datum (k + 1) (a + 1)) : DatumCode :=
  ((k, a), ((List.ofFn fun i => List.ofFn fun j => (data.designated i j).val),
    data.polynomials.map fun p => (p.1, p.2.map fun term => (List.ofFn term.1, term.2))))
def supports (data : DatumCode) : ComputableCone.SupportsCode :=
  data.2.2.map fun p => p.2.map Prod.fst
def vectorLength (k : ℕ) (v : List ℤ) : ℕ :=
  ((List.range k).map fun i => (v.getD i 0).natAbs).sum
def lengthBound (data : DatumCode) : ℕ :=
  1 + (data.2.2.flatMap fun p => p.2.map fun term => vectorLength (dimension data) term.1).sum
def radius (data : DatumCode) (r : ℕ) : ℕ :=
  1 + 2 * dimension data * (1 + lengthBound data +
    lengthBound data ^ 2 * dimension data * 2 ^ r)
def check (data : DatumCode) (r : ℕ) : Bool :=
  ComputableCone.checkMargin (dimension data, r) (supports data)
end Kourovka.MetabelianEnumeration.ComputableCoverData


