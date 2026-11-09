-- Prove2me | Definitions.Def_Couret_RectangleProbes_c3e716b02120
-- name    : Couret_RectangleProbes_c3e716b02120
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:08.527982+00:00
-- url     : https://prove2.me/theorems/b2b1b459-2d7e-454c-83cc-5133ee75c1a0
-- title:
--   An affine rectangle of real observations
-- statement:
--   For functions $H,U,V:I\to\mathbb R$ and two Boolean parameters $(p_1,p_2)$, defines the function $H+p_1U+p_2V$, interpreting false as zero and true as one. This parametrizes four candidate observations for fixed-coordinate separation arguments.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/RectangleProbes.lean; source file SHA-256 2a9d979b50edf3a1856fc7ac02e8ea5dce341c04960af2e3dd959cf365aecc5c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace Couret.InterIA.Cubic

def rectangle {ι : Type*} (H U V : ι → ℝ) (p : Bool × Bool) : ι → ℝ :=
  fun z => H z + (if p.1 then U z else 0) + (if p.2 then V z else 0)





end Couret.InterIA.Cubic


