-- Prove2me | Definitions.Def_Couret_FourSignRigidity_4bbe2289ca60
-- name    : Couret_FourSignRigidity_4bbe2289ca60
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:26.228057+00:00
-- url     : https://prove2.me/theorems/14624f4c-8e9a-4dd6-ace1-5bd37a00e999
-- title:
--   Signed polynomial summands
-- statement:
--   A Boolean chooses whether to negate a real polynomial: $$\operatorname{signed}(e,P)=\begin{cases}-P&e=\mathrm{true},\\P&e=\mathrm{false}.\end{cases}$$ This lightweight operation expresses all sign partitions of four summands in the polynomial rigidity argument.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/FourSignRigidity.lean; source file SHA-256 7457f510d3cb5dc7da1d3bc7f820517db19363da66a96ff0fd98a3e1f65bb956

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial









noncomputable def signed (flip : Bool) (p : ℝ[X]) : ℝ[X] := if flip then -p else p







end Couret.InterIA.Fibres


