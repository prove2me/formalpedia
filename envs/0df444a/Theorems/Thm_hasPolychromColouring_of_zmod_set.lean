-- Prove2me | Theorems.Thm_hasPolychromColouring_of_zmod_set
-- name    : hasPolychromColouring_of_zmod_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:11.561669+00:00
-- url     : https://prove2.me/theorems/17baa518-ecf5-4c60-aad2-3152f09cf7d2
-- title:
--   has Polychrom Colouring of zmod set: has Polychrom Colouring of zmod set
-- statement:
--   Auxiliary: lifts polychromaticity from ZMod m back to ℤ, combining the
--       homomorphism ℤ → ZMod m (Lemma 12(ii)) with `polychromNumber_zmod`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L115-L123
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L115-L123

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi
set_option autoImplicit true
open Finset Pointwise

theorem hasPolychromColouring_of_zmod_set {a b c : ℤ} {m : ℕ}
    (hm_eq : (m : ℤ) = c - a + b)
    (h : HasPolychromColouring (Fin 3) (zmod_set m a b)) :
    HasPolychromColouring (Fin 3) ({0, a, b, c} : Finset ℤ) := by sorry
