-- Prove2me | Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
-- name    : Kourovka_Enumeration_EpimorphismEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:25:24.239538+00:00
-- url     : https://prove2.me/theorems/cdb8d572-120f-4379-9549-83833df1ada6
-- title:
--   Epimorphism Enumeration
-- statement:
--   Definitions and structural lemmas for Epimorphism Enumeration, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
set_option autoImplicit true
set_option autoImplicit false
namespace Kourovka.MetabelianEnumeration.EpimorphismEnumeration
abbrev DatumCode := ComputableCoverData.DatumCode
abbrev Certificate := (DatumCode × ℕ) × ℕ
def source (c : Certificate) : PresentationCode :=
  ComputableCoverWords.presentation c.1.1 (ComputableCoverData.radius c.1.1 c.1.2)
def checkData (p : PresentationCode) (c : Certificate) : Bool :=
  decide (WellFormed p) && (decide (p.1 = 0) ||
    (ComputableCoverData.check c.1.1 c.1.2 &&
      ComputableEpimorphism.checkEpi (source c, p) c.2))
def defaultCertificate : Certificate := ((((0, 0), ([], [])), 0), 0)
def decodeCertificate (c : ℕ) : Certificate :=
  (@Encodable.decode Certificate (inferInstance : Primcodable Certificate).toEncodable c).getD
    defaultCertificate
def encodeCertificate (c : Certificate) : ℕ :=
  @Encodable.encode Certificate (inferInstance : Primcodable Certificate).toEncodable c
def check (p c : ℕ) : Bool := checkData (decodePresentation p) (decodeCertificate c)
end Kourovka.MetabelianEnumeration.EpimorphismEnumeration


