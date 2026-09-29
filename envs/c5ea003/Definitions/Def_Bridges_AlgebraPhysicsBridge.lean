-- Prove2me | Definitions.Def_Bridges_AlgebraPhysicsBridge
-- name    : Bridges_AlgebraPhysicsBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:11.165188+00:00
-- url     : https://prove2.me/theorems/90025f80-68eb-418a-bde2-dc4c498a2e82
-- title:
--   Aether Catalog definitions — Bridges_AlgebraPhysicsBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlgebraPhysicsBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlgebraPhysicsBridge.lean by skeleton subtraction
import Mathlib

/-! # Algebra-Physics Bridge: Hilbert-Schmidt Norm

Formal bridge between Algebra and Physics domains.
-/

noncomputable section

namespace AlgebraPhysicsBridge

def hilbertSchmidtNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)



end AlgebraPhysicsBridge


