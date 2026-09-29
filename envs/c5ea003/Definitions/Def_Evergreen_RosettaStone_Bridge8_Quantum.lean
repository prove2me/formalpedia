-- Prove2me | Definitions.Def_Evergreen_RosettaStone_Bridge8_Quantum
-- name    : Evergreen_RosettaStone_Bridge8_Quantum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:39:05.345436+00:00
-- url     : https://prove2.me/theorems/5345dbf8-109d-438a-8013-2a2e5d3a0d35
-- title:
--   Aether Catalog definitions — Evergreen_RosettaStone_Bridge8_Quantum
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.RosettaStone.Bridge8.Quantum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/RosettaStone/Bridge8_Quantum.lean by skeleton subtraction
import Mathlib
/-
  Bridge 8: Quantum Geometry — Projections and Measurements
  ===========================================================
  Measurements are projections (P² = P). Idempotency = measurement stability.
-/

namespace RosettaStone.Quantum

variable {n : ℕ}

/-- A projection matrix P satisfies P² = P. -/
def IsProjection (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P * P = P








/-- A diagonal projection matrix. -/
def diagonalProjection (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if i ∈ S then 1 else 0)



end RosettaStone.Quantum


