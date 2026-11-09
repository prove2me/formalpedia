-- Prove2me | Definitions.Def_Couret_CubicFourier_396e42df2f8b
-- name    : Couret_CubicFourier_396e42df2f8b
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:25.552634+00:00
-- url     : https://prove2.me/theorems/8648fc83-c2d3-4e4a-9aac-f2562ce0a816
-- title:
--   Finite complex additive convolution
-- statement:
--   For complex-valued functions on a finite abelian group, defines convolution at $z$ as $\sum_{x,y:x+y=z}f(x)g(y)$. This supplies the finite Fourier interface for cubic and square-profile arguments.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicFourier.lean; source file SHA-256 c0e1858422dfb02100eea58c200f328f13b0ef1ffe13be5a655bfe101674c789

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset

noncomputable def cconv {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f g : G → ℂ) (z : G) : ℂ :=
  ∑ x, ∑ y, if x+y=z then f x*g y else 0







end Couret.InterIA.Cubic


