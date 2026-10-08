-- Prove2me | Theorems.Thm_RhinViola_psi_invariant_under_tau
-- name    : RhinViola.psi_invariant_under_tau
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T21:23:08.664844+00:00
-- url     : https://prove2.me/theorems/4454c0f9-6dfc-4d72-8a95-9c66a3205afb
-- title:
--   The Rhin–Viola birational transformation preserves Beukers' rational function
-- statement:
--   Let x and y be complex numbers, with x nonzero and 1 - xy nonzero. Define the Rhin–Viola transformation τ(x,y) = ((1-x)/(1-xy), 1-xy) and ψ(x,y) = xy(1-x)(1-y)/(1-xy). Then ψ(τ(x,y)) = ψ(x,y). This is the algebraic invariance in Section 5 of Rhin and Viola (1993), an ingredient in the asymptotic estimates for the irrationality measure of ζ(2). The two nonzero assumptions are sufficient to make both ψ expressions defined as ordinary field divisions.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), Section 5, p. 98, eq. (iv), https://www.numdam.org/article/AIF_1993__43_1_85_0.pdf. Mathematically relevant to Prove2Me PiIrrationality.rhin_viola_bound (bda7f199-9603-4c9e-8825-e30a14d70f09), an Open target. Prove2Me parent-child edge is not yet established.

import Mathlib

theorem RhinViola.psi_invariant_under_tau
    (x y : ℂ) (hx : x ≠ 0) (hxy : 1 - x * y ≠ 0) :
    (fun u v : ℂ => u * v * (1 - u) * (1 - v) / (1 - u * v))
      ((1 - x) / (1 - x * y)) (1 - x * y) =
    (fun u v : ℂ => u * v * (1 - u) * (1 - v) / (1 - u * v)) x y := by sorry
