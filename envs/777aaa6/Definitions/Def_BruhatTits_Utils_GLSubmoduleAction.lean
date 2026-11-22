-- Prove2me | Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
-- name    : BruhatTits_Utils_GLSubmoduleAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:48:52.282546+00:00
-- url     : https://prove2.me/theorems/414b6ffb-4cae-4d2a-9367-9a31a5080bc7
-- title:
--   GLSubmodule Action
-- statement:
--   Definitions and structural lemmas for GLSubmodule Action, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean

import Definitions.Def_BruhatTits_Utils_Matrix
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
namespace BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end BruhatTits


