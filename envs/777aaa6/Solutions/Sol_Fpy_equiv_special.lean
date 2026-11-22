-- Prove2me | solution 1 for Fpy.equiv_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:52:55.351194+00:00
-- url     : https://prove2.me/submissions/6a0b256b-8802-4ab2-9926-4ac7f6b252bc

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_exec_round
import Theorems.Thm_Fpy_exec_round_inv
import Theorems.Thm_Fpy_exec_nanBranch
import Theorems.Thm_Fpy_exec_eqBranch
import Theorems.Thm_Fpy_num_of_nanBranch
import Theorems.Thm_Fpy_num_of_eqBranch
import Theorems.Thm_Fpy_Equiv_of_fwd


set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
namespace Fpy
theorem _root_.solution {C : Val} {r : Num → Num} {x t : Var}
    (hr : C.rnd (fpy decode) = some r) (h0 : r (.finite 0) = .finite 0)
    (kn kneg kpos kz : Bool) :
    Equiv Φ X Γ (some C) (.assign x (.arithOp .round [.var t]))
      (nanBranch r kn x t
        (eqBranch kneg x t (.special (.inf true)) (r (.special (.inf true)))
        (eqBranch kpos x t (.special (.inf false)) (r (.special (.inf false)))
        (eqBranch kz x t (.finite 0) (.finite 0) (.assign x (.arithOp .round [.var t])))))) := by
  refine Equiv.of_fwd (fun σ C₀ o _ hκ hs => ?_) (fun σ C₀ o' _ hκ hs => ?_) <;>
    obtain rfl := hκ C rfl
  · obtain ⟨u, ht, rfl⟩ := exec_round_inv hr hs
    exact ⟨_, exec_nanBranch ht (exec_eqBranch rfl ht (exec_eqBranch rfl ht
      (exec_eqBranch h0 ht (exec_round hr ht) kz) kpos) kneg) kn, Store.Agree.refl _⟩
  · obtain ⟨u, ht⟩ := num_of_nanBranch hs fun _ h => num_of_eqBranch h fun _ h =>
      num_of_eqBranch h fun _ h => num_of_eqBranch h fun _ h =>
        (exec_round_inv hr h).imp fun _ h => h.1
    exact ⟨_, exec_round hr ht⟩
end Fpy
