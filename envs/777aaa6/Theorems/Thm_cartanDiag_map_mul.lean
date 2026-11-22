-- Prove2me | Theorems.Thm_cartanDiag_map_mul
-- name    : cartanDiag_map_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:16:58.707322+00:00
-- url     : https://prove2.me/theorems/ec702271-d202-43ee-bf03-ceceda08ce57
-- title:
--   cartan Diag map mul: cartan Diag map mul
-- statement:
--   The cartan Diag map mul construction uses the cartan Diag map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L35-L48
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean#L35-L48

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
open Matrix

theorem cartanDiag_map_mul {ϖ : R} (hϖ : Irreducible ϖ) {u : Rˣ} (hϖ' : Irreducible (ϖ * u))
    (f : Fin k → ℤ) :
    cartanDiag (ϖ * u.val) hϖ' f =
      (GL.diagonal (fun i ↦ u ^ (f i)) : GL (Fin k) R) * cartanDiag ϖ hϖ f := by sorry
