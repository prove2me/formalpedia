-- Prove2me | solution 1 for Mpfx.Format.mem_unbounded_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:00:25.178883+00:00
-- url     : https://prove2.me/submissions/a1e704d3-339c-4e84-b48f-8632731ee7c6

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_subset_unbounded_of_le

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} {p : Prec} {e : QExp}
    {v : Dyadic} (hp : p ≤ F.p) (he : F.exp ≤ e)
    (hvp : Dyadic.precisionAtMost p v) (hvq : Dyadic.quantumAtLeast e v) :
    v ∈ F.unbounded :=
  subset_unbounded_of_le (G := { p := p, exp := e, b := ⊤, specials := ∅ }) hp he
    (Set.empty_subset _) v ⟨hvp, hvq, trivial⟩
end Mpfx.Format
