-- Prove2me | Theorems.Thm_P2M_BruhatTits_mem_stabilizer_ntwist__iff_mem_span_dd49240cc32d
-- name    : P2M_BruhatTits_mem_stabilizer_ntwist__iff_mem_span_dd49240cc32d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:31.672605+00:00
-- url     : https://prove2.me/theorems/94bf61af-0263-43ba-9447-85fc7e7f9620
-- title:
--   P2 M Bruhat Tits mem stabilizer ntwist  iff mem span dd49240cc32d: P2 M Bruhat Tits mem stabilizer ntwist  iff mem span dd49240cc32d
-- statement:
--   `g` in `GL₂(R)` is in the stabilizer of `(e₀, ϖ ^ n • e₁)` if and only if
--   `g 1 0 ≡ 0 (mod ϖ ^ n)`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L354-L374
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L354-L374

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem P2M_BruhatTits_mem_stabilizer_ntwist__iff_mem_span_dd49240cc32d {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (g : GL (Fin 2) R) :
    (g : GL (Fin 2) K) ∈ MulAction.stabilizer (GL (Fin 2) K)
      ((Basis.ntwist₂ (Pi.basisFun K (Fin 2)) hϖ 0 n).toLattice (R := R)) ↔
    g 1 0 ∈ Ideal.span {ϖ ^ n} := by sorry

alias «BruhatTits».«mem_stabilizer_ntwist₂_iff_mem_span» := P2M_BruhatTits_mem_stabilizer_ntwist__iff_mem_span_dd49240cc32d
