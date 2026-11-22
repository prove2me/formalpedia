-- Prove2me | Definitions.Def_Metabelian16624b89_Kourovka_Paper
-- name    : Metabelian16624b89_Kourovka_Paper
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:27:15.484873+00:00
-- url     : https://prove2.me/theorems/80034abb-714d-4ffa-bbb9-620ac535cc35
-- title:
--   Paper
-- statement:
--   Definitions and structural lemmas for Paper, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Paper.lean

import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.Paper
abbrev certificateCheck : ℕ → ℕ → Bool := EpimorphismEnumeration.check
end Kourovka.MetabelianEnumeration.Paper


