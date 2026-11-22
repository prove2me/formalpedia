-- Prove2me | Theorems.Thm_P2M_Matrix_coeffs_sup_toBlock___le_coeffs_sup_ffc25748b245
-- name    : P2M_Matrix_coeffs_sup_toBlock___le_coeffs_sup_ffc25748b245
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:38.674457+00:00
-- url     : https://prove2.me/theorems/285f5ba7-8d9d-4bb0-9bda-71b3278fe2cc
-- title:
--   P2 M Matrix coeffs sup to Block   le coeffs sup ffc25748b245: P2 M Matrix coeffs sup to Block   le coeffs sup ffc25748b245
-- statement:
--   The P2 M Matrix coeffs sup to Block   le coeffs sup ffc25748b245 construction uses the P2 M Matrix coeffs sup to Block   le coeffs sup ffc25748b245 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L269-L273
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L269-L273

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
set_option autoImplicit false
open BigOperators
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R]
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
variable [DecidableEq m] [Fintype n] [Fintype m]
variable [Fintype n'] [Nonempty n'] [Fintype m'] [Nonempty m']
variable [DecidableEq n'] [DecidableEq m']
omit [DecidableEq m] [DecidableEq n'] [DecidableEq m']

theorem P2M_Matrix_coeffs_sup_toBlock___le_coeffs_sup_ffc25748b245 [Nonempty n] (g : Matrix (n ⊕ n') (m' ⊕ m) R) :
    g.toBlocks₁₁.coeffs_sup v ≤ g.coeffs_sup v := by sorry

alias «Matrix».«coeffs_sup_toBlock₁₁_le_coeffs_sup» := P2M_Matrix_coeffs_sup_toBlock___le_coeffs_sup_ffc25748b245
