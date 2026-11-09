-- Prove2me | Theorems.Thm_Couret_Certificate_exactly_146_nonempty_reachable
-- name    : Couret.Certificate.exactly_146_nonempty_reachable
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:47.58455+00:00
-- url     : https://prove2.me/theorems/96d524ea-18ff-412b-b7e7-f2db15ca2d93
-- title:
--   Exactly 146 semantic states are reachable by nonempty words
-- statement:
--   Let $D:\{0,\ldots,145\}\to\operatorname{State}(\mathrm{Code}_{30})$ decode table entries 1 through 146. Then $D$ is injective, and for every semantic state $s$,
--
--   $$\bigl(\exists w\ne\varnothing:\operatorname{run}(w)=s\bigr)\Longleftrightarrow\bigl(\exists i<146:D(i)=s\bigr).$$
--
--   Here words use the eight unit residues modulo 30 and run denotes the modulo-30 support automaton. Thus precisely 146 distinct semantic states occur for nonempty words.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/CertificateProofs.lean, lines 74–107; source file SHA-256 34105504de63d99f05e7d3427ba82853380bac1d8c053b618776cd7d98da83b2; theorem Couret.Certificate.exactly_146_nonempty_reachable

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_Certificate_StepValid_sound
import Theorems.Thm_Couret_Certificate_decode_injective
import Theorems.Thm_Couret_Certificate_entry_injective
import Theorems.Thm_Couret_Certificate_initial_encoding
import Theorems.Thm_Couret_Certificate_nonempty_witness_checked
import Theorems.Thm_Couret_Certificate_reachability_checked
import Theorems.Thm_Couret_Certificate_symbol_code
import Theorems.Thm_Couret_Certificate_transitions_checked
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate

theorem exactly_146_nonempty_reachable :
    (∀ i j : Fin 146, noninitialDecoded i = noninitialDecoded j → i = j) ∧
    (∀ s : State Code30,
      (∃ w : Word Code30, w.nonempty ∧ run mod30Product w = s) ↔
        ∃ i : Fin 146, noninitialDecoded i = s) := by sorry






















































end Certificate
end Couret
