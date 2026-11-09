-- Prove2me | Definitions.Def_Couret_CubicReconstruction_bc5d14805c7e
-- name    : Couret_CubicReconstruction_bc5d14805c7e
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:12:10.25876+00:00
-- url     : https://prove2.me/theorems/59c1b04d-1deb-427f-99db-39aa98510c6e
-- title:
--   Real cubic-convolution readings
-- statement:
--   For a finite support $S$ in an abelian group, the real cubic reading records the triple-convolution coefficient of its indicator: $$C_S(z)=(1_S*1_S*1_S)(z).$$ This supplies the probe function used to distinguish supports within a fixed ordered-square fibre.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicReconstruction.lean; source file SHA-256 c905b6a3c806a78c1db7ac9770bb76ec0a760869eeb7c80eacd35ac1d736463b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CubicSupport_513df21f9351
import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

noncomputable def realCube {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) : G → ℝ := fun z => (orderedCube S z : ℝ)







end Couret.InterIA.Cubic


