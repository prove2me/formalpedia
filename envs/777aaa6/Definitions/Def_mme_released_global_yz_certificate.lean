-- Prove2me | Definitions.Def_mme_released_global_yz_certificate
-- name    : mme_released_global_yz_certificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T13:01:08.70304+00:00
-- url     : https://prove2.me/theorems/55509961-3d62-4238-ae28-9cb8186998b8
-- title:
--   Exact global Y/Z certificate: certificate
-- statement:
--   One component of the exact six-orientation Y/Z certificate: word enumeration and cached integer counts, finite entropy expressions, or outward-rounded logarithm intervals. All numerical data are connected to the published profile by the accompanying full proofs. Tables are split by orientation to fit publication and compilation limits.
-- source:
--   Exact released global candidate from primitive seed f8187420c24231b83d9d1fb7b327fee76cd50ada0af0525e77b3d3b0d8f4d4e6.

import Definitions.Def_mme_released_global_yz_logs_0
import Definitions.Def_mme_released_global_yz_logs_1
import Definitions.Def_mme_released_global_yz_logs_2
import Definitions.Def_mme_released_global_yz_logs_3
import Definitions.Def_mme_released_global_yz_logs_4
import Definitions.Def_mme_released_global_yz_logs_5
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace MME.ReleasedGlobalYZ

def entries : Fin 6 → Fin 2 → List Entry := ![entriesOwner0,entriesOwner1,entriesOwner2,entriesOwner3,entriesOwner4,entriesOwner5]

def entryBound (e : Entry) : ℚ := e.1.1 * (if 0 ≤ e.1.1 then e.2.2.1 else e.2.2.2)
def totalBound (o : Fin 6) (i : Fin 2) : ℚ := ((entries o i).map entryBound).sum

end MME.ReleasedGlobalYZ


