-- Prove2me | Definitions.Def_Kourovka_Certificates_NaturalWordCertificates
-- name    : Kourovka_Certificates_NaturalWordCertificates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:43:47.293852+00:00
-- url     : https://prove2.me/theorems/472cf27f-c32c-44e4-910a-6633a0c6421c
-- title:
--   Natural Word Certificates
-- statement:
--   Definitions and structural lemmas for Natural Word Certificates, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordCertificates.lean

import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.NaturalWordCertificates
open ComputablePresentations NaturalWordSubstitution
abbrev Input := PresentationCode × Word
def checkList (inputs : List Input) (certs : List ℕ) : Bool :=
  decide (∀ i ∈ List.range inputs.length,
    checkTrivial (inputs.getD i ((0, []), [])) (certs.getD i 0) = true)
def Good (input : Input) : Prop :=
  validInput input ∧ PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1
end Kourovka.MetabelianEnumeration.NaturalWordCertificates


