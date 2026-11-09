-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_square_cube_injective
-- name    : Couret.InterIA.Cubic.square_cube_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:30.913826+00:00
-- url     : https://prove2.me/theorems/8e25a8d1-1f2d-447f-b4a6-28bb4a4ea547
-- title:
--   Square and cube determine a cyclic function
-- statement:
--   For $n\ne0$ and complex-valued functions $f,g$ on $\mathbb Z/n$, equality of their cyclic convolution squares and cubes implies $$f*f=g*g,\quad(f*f)*f=(g*g)*g\Longrightarrow f=g.$$ No positivity or support assumption is required.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicFourier.lean, lines 52–62; source file SHA-256 c0e1858422dfb02100eea58c200f328f13b0ef1ffe13be5a655bfe101674c789; theorem Couret.InterIA.Cubic.square_cube_injective

import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Cubic_dft_cconv
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset

theorem square_cube_injective {n : ℕ} [NeZero n] (f g : ZMod n → ℂ)
    (hs : cconv f f = cconv g g)
    (hc : cconv (cconv f f) f = cconv (cconv g g) g) : f=g := by sorry


end Couret.InterIA.Cubic
