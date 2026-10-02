-- Prove2me | solution 1 for ProofsInTheBook.Chapter08.chapter08_basel
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T14:43:37.290489+00:00
-- url     : https://prove2.me/submissions/12492051-2135-4c33-9096-1b3e3d3d43e4

import Mathlib


/-!
# Chapter 8: Three times π²/6

From "Proofs from THE BOOK":

**The Basel problem**: ∑_{k=1}^∞ 1/k² = π²/6.

The book presents three proofs:
1. Euler's original proof via the product formula for sin(x)/x.
2. A proof using Parseval's identity for Fourier series.
3. A proof using the substitution x = π·t in ∫₀¹ log(sin πt) dt.

All three establish that ζ(2) = π²/6.
-/

namespace ProofsInTheBook.Chapter08

open Real

/-!
### The Basel problem: ∑ 1/k² = π²/6

*Book proof 1 (Euler).* From the product formula sin(x)/x = ∏(1 - x²/(n²π²)),
expand and compare the x² coefficient: -1/6 = -∑ 1/(n²π²), giving ∑ 1/n² = π²/6.

*Book proof 2 (Parseval).* Apply Parseval's identity to f(x) = x on [-π, π]:
∑ |cₙ|² = (1/2π) ∫ |f|², computing Fourier coefficients explicitly.
-/









end ProofsInTheBook.Chapter08

open Real
open ProofsInTheBook.Chapter08

theorem solution : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  hasSum_zeta_two
