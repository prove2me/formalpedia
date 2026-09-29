-- Prove2me | Definitions.Def_Bridges_HilbertSpace_AlgebraPhysicsBridge
-- name    : Bridges_HilbertSpace_AlgebraPhysicsBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:08.667539+00:00
-- url     : https://prove2.me/theorems/c7e116ed-1c1c-47b8-bc01-31fe47cfb9e5
-- title:
--   Aether Catalog definitions — Bridges_HilbertSpace_AlgebraPhysicsBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.HilbertSpace.AlgebraPhysicsBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/HilbertSpace/AlgebraPhysicsBridge.lean by skeleton subtraction
import Mathlib

/-! # Algebra-Physics Bridge: Hilbert-Schmidt Norm

Formal bridge between Algebra and Physics domains.
-/

noncomputable section

namespace AlgebraPhysicsBridge

def hilbertSchmidtNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)



end AlgebraPhysicsBridge


