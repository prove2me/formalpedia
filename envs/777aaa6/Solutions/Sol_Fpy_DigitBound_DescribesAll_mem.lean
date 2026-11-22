-- Prove2me | solution 1 for Fpy.DigitBound.DescribesAll.mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:21:25.568416+00:00
-- url     : https://prove2.me/submissions/f9d3cb66-d086-4544-9764-3a3c84e67517

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace DescribesAll
theorem _root_.solution {Ψ : List Con} {ι : Asgn} {d : DVal} {a : ℕ} :
    ∀ {vs : List Val}, DescribesAll Ψ ι d a vs → ∀ {v : Val}, v ∈ vs →
      ∃ ι₀, Agree a ι ι₀ ∧ Sat ι₀ Ψ ∧ Describes Ψ ι₀ d v
  | _, .nil, _, hv => absurd hv List.not_mem_nil
  | _, .cons h₀ hs hd tl, _, hv =>
    (List.mem_cons.mp hv).elim (fun h => h ▸ ⟨_, h₀, hs, hd⟩) (fun h => solution tl h)
end DescribesAll
end Fpy.DigitBound
