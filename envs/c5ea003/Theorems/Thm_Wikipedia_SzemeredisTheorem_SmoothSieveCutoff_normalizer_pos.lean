-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_normalizer_pos
-- name    : Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.normalizer_pos
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:37:21.103692+00:00
-- url     : https://prove2.me/theorems/2c15573c-e511-41b9-aa79-b46a8a8d5683
-- title:
--   Positivity of the smooth cutoff normalizer
-- statement:
--   Every smooth sieve cutoff $\chi$ has strictly positive derivative-square normalizer: $0<\chi.\mathrm{normalizer}$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/SmoothCutoff.lean#L91-L126

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/
open Wikipedia.SzemeredisTheorem
open Function Set MeasureTheory
open scoped ContDiff
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff

theorem Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.normalizer_pos (χ : SmoothSieveCutoff) :
    0 < χ.normalizer := by sorry
