-- Prove2me | solution 1 for Fpy.EvalList.num_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:00:31.062928+00:00
-- url     : https://prove2.me/submissions/45f05675-8bfa-4942-9a18-dca3680e2dea

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}
namespace Fpy
namespace EvalList
theorem _root_.solution : ∀ {es : List (Expr L)} {ns : List Num},
    EvalList Φ σ C es (ns.map .num) → ∀ e ∈ es, ∃ u, Eval Φ σ C e (.num u) := by
  intro es
  induction es with
  | nil => intro _ _ e he; exact absurd he List.not_mem_nil
  | cons e es ih =>
    intro ns h e' he
    rcases ns with _ | ⟨u, ns⟩
    · cases h
    · cases h with
      | cons h₁ hs =>
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨u, h₁⟩
        · exact ih hs e' he
end EvalList
end Fpy
