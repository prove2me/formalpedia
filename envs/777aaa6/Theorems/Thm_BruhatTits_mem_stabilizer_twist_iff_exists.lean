-- Prove2me | Theorems.Thm_BruhatTits_mem_stabilizer_twist_iff_exists
-- name    : BruhatTits.mem_stabilizer_twist_iff_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:57.044829+00:00
-- url     : https://prove2.me/theorems/0eca1b19-a2b1-461a-a471-2829065aa629
-- title:
--   Bruhat Tits: mem stabilizer twist iff exists
-- statement:
--   `g` in `GL₂(K)` stabilizes `(ϖ ^ n • e₀, ϖ ^ m • e₁)` if and only if `g` is of the form
--   ```
--         a           ϖ ^ (n - m) * b
--   ϖ ^ (m - n) * c         d
--   ```
--   for some `(a b, c d)` in `GL₂(R)`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L333-L350
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L333-L350

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.mem_stabilizer_twist_iff_exists {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) K)
    (f : Fin 2 → ℤ) :
    g ∈ MulAction.stabilizer (GL (Fin 2) K)
      ((Basis.twist (Pi.basisFun K (Fin 2)) hϖ f).toLattice (R := R)) ↔
    ∃ (k : GL (Fin 2) R),
      g 0 0 = k 0 0 ∧
      g 1 1 = k 1 1 ∧
      g 1 0 = ϖ ^ (f 1 - f 0) * k 1 0 ∧
      g 0 1 = ϖ ^ (f 0 - f 1) * k 0 1 := by sorry
