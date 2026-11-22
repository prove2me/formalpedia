-- Prove2me | Theorems.Thm_BruhatTits_eq_signature_iff
-- name    : BruhatTits.eq_signature_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:24.547098+00:00
-- url     : https://prove2.me/theorems/4a85e065-d609-4f9f-9888-cf519d3c74e5
-- title:
--   Bruhat Tits: eq signature iff
-- statement:
--   To show that an antitone pair of integers `fᵢ` is the signature of `M` and `L` it
--   suffices to find basis that satisfy the defining property of the signature.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L249-L262
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L249-L262

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits

theorem BruhatTits.eq_signature_iff (M L : BruhatTits.Lattice R)
    (f : Fin 2 → ℤ) (hf : Antitone f) :
    signature M L = f ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      Irreducible ϖ ∧ ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val := by sorry
