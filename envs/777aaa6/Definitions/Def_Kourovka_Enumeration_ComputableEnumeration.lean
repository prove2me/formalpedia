-- Prove2me | Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
-- name    : Kourovka_Enumeration_ComputableEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:49:11.332407+00:00
-- url     : https://prove2.me/theorems/af1198e0-5af8-409f-8cc1-ea5df21a74c4
-- title:
--   Computable Enumeration
-- statement:
--   Definitions and structural lemmas for Computable Enumeration, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
set_option autoImplicit true
set_option autoImplicit false
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
abbrev DatumCode := ComputableCoverData.DatumCode
abbrev ExtraRelators := List (List (ℕ × Bool))
abbrev Certificate := (DatumCode × ℕ) × (ExtraRelators × ℕ)
instance (p : PresentationCode) : Decidable (WellFormed p) := by
  unfold WellFormed
  infer_instance
def source (c : Certificate) : PresentationCode :=
  ComputableCoverWords.presentation c.1.1 (ComputableCoverData.radius c.1.1 c.1.2)
def extended (c : Certificate) : PresentationCode :=
  QuotientCodes.appendRelators (source c) c.2.1
def checkData (p : PresentationCode) (c : Certificate) : Bool :=
  decide (WellFormed p) && (decide (p.1 = 0) ||
    (ComputableCoverData.check c.1.1 c.1.2 &&
      ComputableIsomorphism.checkIso (extended c, p) c.2.2))
def defaultCertificate : Certificate := ((((0, 0), ([], [])), 0), ([], 0))
def decodeCertificate (c : ℕ) : Certificate :=
  (@Encodable.decode Certificate (inferInstance : Primcodable Certificate).toEncodable c).getD
    defaultCertificate
def encodeCertificate (c : Certificate) : ℕ :=
  @Encodable.encode Certificate (inferInstance : Primcodable Certificate).toEncodable c
def check (p c : ℕ) : Bool := checkData (decodePresentation p) (decodeCertificate c)
end Kourovka.MetabelianEnumeration.ComputableEnumeration


