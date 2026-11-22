-- Prove2me | Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
-- name    : Kourovka_Certificates_ComputableIsomorphism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:18.556563+00:00
-- url     : https://prove2.me/theorems/522fa8a6-5e66-4141-b1cf-f437568f50d7
-- title:
--   Computable Isomorphism
-- statement:
--   Definitions and structural lemmas for Computable Isomorphism, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/ComputableIsomorphism.lean

import Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
abbrev Maps := Images × Images
abbrev MapInput := (PresentationCode × PresentationCode) × Maps
abbrev Certificate := Maps × List ℕ
def validMaps (d : MapInput) : Prop :=
  WellFormed d.1.1 ∧ WellFormed d.1.2 ∧
    d.2.1.length = d.1.1.1 ∧ d.2.2.length = d.1.2.1 ∧
      WellFormed (d.1.2.1, d.2.1) ∧ WellFormed (d.1.1.1, d.2.2)
instance : DecidablePred validMaps := fun d => by
  unfold validMaps WellFormed
  infer_instance
def relatorChecks (d : PresentationCode × (PresentationCode × Images)) : List Input :=
  d.1.2.map fun w => (d.2.1, substitute d.2.2 w)
def inverseChecks (d : PresentationCode × Maps) : List Input :=
  (List.range d.1.1).map fun i =>
    (d.1, substitute d.2.2 (d.2.1.getD i []) ++ [(i, false)])
def obligations (d : MapInput) : List Input :=
  relatorChecks (d.1.1, (d.1.2, d.2.1)) ++
    relatorChecks (d.1.2, (d.1.1, d.2.2)) ++
      inverseChecks (d.1.1, (d.2.1, d.2.2)) ++
        inverseChecks (d.1.2, (d.2.2, d.2.1))
def checkData (pq : PresentationCode × PresentationCode) (c : Certificate) : Bool :=
  decide (validMaps (pq, c.1)) && checkList (obligations (pq, c.1)) c.2
def decodeCertificate (n : ℕ) : Certificate := (Encodable.decode n).getD (([], []), [])
def checkIso (pq : PresentationCode × PresentationCode) (n : ℕ) : Bool :=
  checkData pq (decodeCertificate n)
end Kourovka.MetabelianEnumeration.ComputableIsomorphism


