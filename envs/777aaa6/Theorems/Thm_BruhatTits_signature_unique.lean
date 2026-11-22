-- Prove2me | Theorems.Thm_BruhatTits_signature_unique
-- name    : BruhatTits.signature_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:11.269181+00:00
-- url     : https://prove2.me/theorems/7cfe4743-d97b-4673-973d-5e9d8363c61f
-- title:
--   Bruhat Tits: signature unique
-- statement:
--   The integers `fᵢ` of `BruhatTits.exists_normal_basis` are unique. More precisely,
--   given two lattices `M` and `L`, uniformizers `ϖ`, `ϖ'`, basis
--   `bM`, `bM'` of `M` and `bL`, `bL'` of `L` and integers `fᵢ`, `fᵢ'` such that
--   `bLᵢ = ϖ ^ fᵢ • bMᵢ` and `bL'ᵢ = ϖ' ^ f'ᵢ • bM'ᵢ` and with `f₂ ≥ f₁`, `f'₁ ≥ f'₂`,
--   then `fᵢ = fᵢ'`. This unique pair of integers `fᵢ` is called the signature of `L` and `M`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L165-L203
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L165-L203

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

theorem BruhatTits.signature_unique {M L : BruhatTits.Lattice R}
    {ϖ ϖ' : R} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    {bM bM' : Basis (Fin 2) R M.M} {bL bL' : Basis (Fin 2) R L.M}
    {f f' : Fin 2 → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val)
    (h' : ∀ i, (bL' i).val = (ϖ' ^ f' i : K) • (bM' i).val) :
    f = f' := by sorry
