-- Prove2me | Definitions.Def_BookSixthRotTriple
-- name    : BookSixthRotTriple
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T04:49:39.492515+00:00
-- url     : https://prove2.me/theorems/e7234bf9-3c64-401b-a1dd-09ad4e1c1529

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3

open scoped BigOperators
open BookSixth

noncomputable section

namespace BookSixth

/-- The threefold rotation at time `t`, as a `ContinuousLinearMap`. -/
def rotTriple (t θ1 θ2 θ3 : ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ((rot12CLM (t * θ3)).comp (rot02CLM (t * θ2))).comp (rot01CLM (t * θ1))

end BookSixth


-- Continuity of the rotation family in time, for each fixed vector.

end


