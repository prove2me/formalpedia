-- Prove2me | Definitions.Def_Kourovka_Covers_ComputableCoverWords
-- name    : Kourovka_Covers_ComputableCoverWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:48:22.264462+00:00
-- url     : https://prove2.me/theorems/9332f6ea-6a8d-4533-9973-91d827800e6c
-- title:
--   Computable Cover Words
-- statement:
--   Definitions and structural lemmas for Computable Cover Words, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData
abbrev WordGroup := FreeGroup ℕ
def ordered (k : ℕ) (v : List ℤ) : WordGroup :=
  ((List.range k).map fun i => FreeGroup.of i ^ v.getD i 0).prod
def polynomial (k : ℕ) (x : WordGroup) (p : PolynomialCode) : WordGroup :=
  (p.2.map fun term => FiniteCover.conjugate (x ^ term.2)
    (bif p.1 then ordered k term.1 else (ordered k term.1)⁻¹)).prod
def designated (data : DatumCode) (i j : ℕ) : ℕ :=
  ((data.2.1.getD i []).getD j 0) % alphabet data
def tRelators (data : DatumCode) : List WordGroup :=
  (List.range (dimension data)).flatMap fun i =>
    ((List.range (dimension data)).filter fun j => i < j).map fun j =>
      FiniteCover.rightComm (FreeGroup.of i) (FreeGroup.of j) *
        (FreeGroup.of (dimension data + designated data i j))⁻¹
def shortRelators (data : DatumCode) (R : ℕ) : List WordGroup :=
  (List.range (alphabet data)).flatMap fun i =>
    (List.range (alphabet data)).flatMap fun j =>
      (ComputableLatticeBall.ball (dimension data) R).map fun v =>
        FiniteCover.rightComm (FreeGroup.of (dimension data + i))
          (FiniteCover.conjugate (FreeGroup.of (dimension data + j)) (ordered (dimension data) v))
def polynomialRelators (data : DatumCode) : List WordGroup :=
  (List.range (alphabet data)).flatMap fun i => data.2.2.map fun p =>
    (FreeGroup.of (dimension data + i))⁻¹ *
      polynomial (dimension data) (FreeGroup.of (dimension data + i)) p
def relators (data : DatumCode) (R : ℕ) : List WordGroup :=
  tRelators data ++ shortRelators data R ++ polynomialRelators data
def presentation (data : DatumCode) (R : ℕ) : PresentationCode :=
  (dimension data + alphabet data, (relators data R).map FreeGroup.toWord)
def tRelator (p : DatumCode × (ℕ × ℕ)) : WordGroup :=
  FiniteCover.rightComm (FreeGroup.of p.2.1) (FreeGroup.of p.2.2) *
    (FreeGroup.of (dimension p.1 + designated p.1 p.2.1 p.2.2))⁻¹
def shortRelator (p : DatumCode × ((ℕ × ℕ) × List ℤ)) : WordGroup :=
  FiniteCover.rightComm (FreeGroup.of (dimension p.1 + p.2.1.1))
    (FiniteCover.conjugate (FreeGroup.of (dimension p.1 + p.2.1.2))
      (ordered (dimension p.1) p.2.2))
def polynomialRelator (p : (DatumCode × ℕ) × PolynomialCode) : WordGroup :=
  (FreeGroup.of (dimension p.1.1 + p.1.2))⁻¹ *
    polynomial (dimension p.1.1) (FreeGroup.of (dimension p.1.1 + p.1.2)) p.2
end Kourovka.MetabelianEnumeration.ComputableCoverWords


