-- Prove2me | Definitions.Def_Geometry_FunctionalObservationStability
-- name    : Geometry_FunctionalObservationStability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:16:39.56774+00:00
-- url     : https://prove2.me/theorems/64be2807-9e95-4694-984c-2bc6a9e2e382
-- title:
--   Aether Catalog definitions — Geometry_FunctionalObservationStability
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.FunctionalObservationStability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/FunctionalObservationStability.lean by skeleton subtraction
import Mathlib

/-!
# Robust functional observation: a bridge to statistical reconstruction

A functional observation `F : X → B` may send two states close together while an
experience observable `E : X → Y` keeps them far apart.  Any Lipschitz decoder
`R : B → Y` must then pay reconstruction error.  The theorem below identifies this
obstruction quantitatively and interprets the average error on the two states as the
risk under their uniform two-point probability distribution.

Unlike the exact fibre obstruction, the result is stable: an observation discrepancy
of at most `ε` can explain at most `K ε` of the experiential contrast when the decoder
is `K`-Lipschitz.  Everything else is forced into reconstruction risk.
-/

namespace FunctionalObservationStability

/-- Mean absolute reconstruction loss for the uniform probability distribution on two
states.  This is the expected metric loss of a decoder on that two-point experiment. -/
noncomputable def pairRisk {X B Y : Type*} [PseudoMetricSpace Y]
    (F : X → B) (E : X → Y) (R : B → Y) (x z : X) : ℝ :=
  (dist (E x) (R (F x)) + dist (E z) (R (F z))) / 2




end FunctionalObservationStability


