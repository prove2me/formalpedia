-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_dft_cconv
-- name    : Couret.InterIA.Cubic.dft_cconv
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:50.952199+00:00
-- url     : https://prove2.me/theorems/cd0dc690-fa60-4403-84b5-e2234cb873ae
-- title:
--   The discrete Fourier transform turns convolution into multiplication
-- statement:
--   Let $n>0$, $f,g:\mathbb Z/n\mathbb Z\to\mathbb C$, and $k\in\mathbb Z/n\mathbb Z$. With unnormalized Fourier transform $\widehat f(k)=\sum_x e^{-2\pi i xk/n}f(x)$ and convolution $f*g(z)=\sum_{x+y=z}f(x)g(y)$,
--
--   $$\widehat{f*g}(k)=\widehat f(k)\widehat g(k).$$
--
--   This diagonalizes cyclic convolution.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/CubicFourier.lean, lines 12–38; source file SHA-256 c0e1858422dfb02100eea58c200f328f13b0ef1ffe13be5a655bfe101674c789; theorem Couret.InterIA.Cubic.dft_cconv

import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset

theorem dft_cconv {n : ℕ} [NeZero n] (f g : ZMod n → ℂ) (k : ZMod n) :
    ZMod.dft (cconv f g) k = ZMod.dft f k * ZMod.dft g k := by sorry






end Couret.InterIA.Cubic
