-- Prove2me | Definitions.Def_BruhatTits_Cartan_Uniqueness
-- name    : BruhatTits_Cartan_Uniqueness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T10:10:27.235694+00:00
-- url     : https://prove2.me/theorems/78cbfa6b-c49d-4111-960d-fdce4679527d
-- title:
--   Uniqueness
-- statement:
--   Definitions and structural lemmas for Uniqueness, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Cartan/Uniqueness.lean

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
section
variable {ϖ : R} {hϖ : Irreducible ϖ}
end


