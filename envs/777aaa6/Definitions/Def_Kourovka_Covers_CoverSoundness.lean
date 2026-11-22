-- Prove2me | Definitions.Def_Kourovka_Covers_CoverSoundness
-- name    : Kourovka_Covers_CoverSoundness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:45:28.351569+00:00
-- url     : https://prove2.me/theorems/37104ac9-556a-4fbb-8f69-a64e7ea9e674
-- title:
--   Cover Soundness
-- statement:
--   Definitions and structural lemmas for Cover Soundness, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/CoverSoundness.lean

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]
def groupT {k a : ℕ} (data : Datum k a) (R : ℕ) (i : Fin k) : GroupOf data R :=
  PresentedGroup.of (Fin.castAdd a i)
def groupA {k a : ℕ} (data : Datum k a) (R : ℕ) (i : Fin a) : GroupOf data R :=
  PresentedGroup.of (Fin.natAdd k i)
end Kourovka.MetabelianEnumeration.FiniteCover


