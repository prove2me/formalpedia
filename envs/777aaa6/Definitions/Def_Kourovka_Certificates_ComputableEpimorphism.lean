-- Prove2me | Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
-- name    : Kourovka_Certificates_ComputableEpimorphism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:46.552318+00:00
-- url     : https://prove2.me/theorems/7da38f50-b143-4c06-88f2-b5e5d10c92d6
-- title:
--   Computable Epimorphism
-- statement:
--   Definitions and structural lemmas for Computable Epimorphism, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableEpimorphism.lean

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
abbrev Maps := ComputableIsomorphism.Maps
abbrev MapInput := ComputableIsomorphism.MapInput
abbrev Certificate := ComputableIsomorphism.Certificate
abbrev validMaps := ComputableIsomorphism.validMaps
def obligations (d : MapInput) : List Input :=
  ComputableIsomorphism.relatorChecks (d.1.1, (d.1.2, d.2.1)) ++
    ComputableIsomorphism.inverseChecks (d.1.2, (d.2.2, d.2.1))
def checkData (pq : PresentationCode × PresentationCode) (c : Certificate) : Bool :=
  decide (validMaps (pq, c.1)) && checkList (obligations (pq, c.1)) c.2
def decodeCertificate (n : ℕ) : Certificate := (Encodable.decode n).getD (([], []), [])
def checkEpi (pq : PresentationCode × PresentationCode) (n : ℕ) : Bool :=
  checkData pq (decodeCertificate n)
end Kourovka.MetabelianEnumeration.ComputableEpimorphism


