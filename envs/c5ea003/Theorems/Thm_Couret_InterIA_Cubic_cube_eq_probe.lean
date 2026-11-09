-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_cube_eq_probe
-- name    : Couret.InterIA.Cubic.cube_eq_probe
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:49.187197+00:00
-- url     : https://prove2.me/theorems/3069d00e-e08f-4807-8615-aafc57b88dca
-- title:
--   The cubic profile is a probe of the common square profile
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $S,T$ be finite subsets of an abelian group with $R_S=R_T$. Let $C_T(z)$ count ordered triples of $T$ with sum $z$, and set $P_f(T)(z)=\sum_{t\in T}f(z-t)$. Then, as real-valued functions,
--
--   $$C_T=P_{R_S}(T).$$
--
--   This expresses cubic information as a linear probe within a square-profile fibre.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicSupport.lean, lines 95–99; source file SHA-256 86b6a418d9e2de393ac4913cf0aea258d411abf4d8e8d64d56470cdd2f3eb82d; theorem Couret.InterIA.Cubic.cube_eq_probe

import Definitions.Def_Couret_CubicSupport_513df21f9351
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity

theorem cube_eq_probe {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S T : Finset G) (hs : ∀ z, orderedSquare S z=orderedSquare T z) :
    (fun z => (orderedCube T z : ℝ)) = probe (fun z => (orderedSquare S z : ℝ)) T := by sorry


end Couret.InterIA.Cubic
