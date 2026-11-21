-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.eq_or_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:48:09.42515+00:00
-- url     : https://prove2.me/submissions/69575fa8-1a00-48a5-bc3f-7eae98c23bdb

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_unique_toNegative
import Theorems.Thm_Mpfx_RoundsFinite_unique_toPositive

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (h : IsFaithfulRound F x y) : y = d ∨ y = u :=
  h.imp (RoundsFinite.unique_toNegative · hd) (RoundsFinite.unique_toPositive · hu)
end IsFaithfulRound
end Mpfx
