-- Prove2me | Definitions.Def_Couret_CubicSupport_513df21f9351
-- name    : Couret_CubicSupport_513df21f9351
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:10.670973+00:00
-- url     : https://prove2.me/theorems/5982519d-56dc-441b-9b68-11da45bfbbbc
-- title:
--   Cubic convolution counts and scalar probes
-- statement:
--   For a finite support $S$ in an abelian group, its ordered-cube count is $C_S(z)=\sum_{x\in S}Q_S(z-x)$. The bundle also defines the complex indicator of $S$ and the real probe $z\mapsto\sum_{x\in S}r(z-x)$ for a real-valued kernel $r$.
--
--   These definitions connect combinatorial pair/triple counts to convolution and measurement functions.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicSupport.lean; source file SHA-256 86b6a418d9e2de393ac4913cf0aea258d411abf4d8e8d64d56470cdd2f3eb82d

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

def orderedCube {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (z : G) : ℕ :=
  ∑ x ∈ S, orderedSquare S (z-x)

noncomputable def complexIndicator {G : Type*} [DecidableEq G] (S : Finset G) : G → ℂ :=
  fun x => if x ∈ S then 1 else 0











noncomputable def probe {G : Type*} [AddCommGroup G] [DecidableEq G]
    (r : G → ℝ) (S : Finset G) : G → ℝ :=
  fun z => ∑ x ∈ S, r (z-x)





end Couret.InterIA.Cubic


