-- Prove2me | Theorems.Thm_Mpfx_Format_mem_unbounded_of_le
-- name    : Mpfx.Format.mem_unbounded_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:38:54.489046+00:00
-- url     : https://prove2.me/theorems/9e36d276-fbf2-4cda-8d5e-c5db5b3d4a4e
-- title:
--   Format: mem unbounded of le
-- statement:
--   Membership form of `subset_unbounded_of_le`: a value whose precision is at
--   most `p ≤ F.p` and whose quantum is at least `e ≥ F.exp` lies in `F.unbounded`.
--   The intermediate format `𝒜(p, e, ⊤)` witnesses the containment, so operations
--   need only exhibit their result's precision/quantum and the format-widening
--   inequalities.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L89-L94
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L89-L94

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.mem_unbounded_of_le {F : Format} {p : Prec} {e : QExp}
    {v : Dyadic} (hp : p ≤ F.p) (he : F.exp ≤ e)
    (hvp : Dyadic.precisionAtMost p v) (hvq : Dyadic.quantumAtLeast e v) :
    v ∈ F.unbounded := by sorry
