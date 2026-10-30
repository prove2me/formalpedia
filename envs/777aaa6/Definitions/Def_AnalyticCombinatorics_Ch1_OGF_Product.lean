-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Product
-- name    : AnalyticCombinatorics_Ch1_OGF_Product
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:32:25.699691+00:00
-- url     : https://prove2.me/theorems/212679f8-25b2-4ad4-a90e-a4ebd293bf99
-- title:
--   Finite Cartesian products with additive sizes
-- statement:
--   A size-n product object is an ordered pair of component objects whose natural sizes sum to n. The finite construction sums over all possible first sizes k from 0 through n and pairs the size-k fibre with the size-(n−k) fibre.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Product.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2 — The Cartesian product construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, the product construction, the
heart of the symbolic method. If `A = B × C` (an object of size `n` is an
ordered pair `(β, γ)` with `|β| + |γ| = n`), then

  `Aₙ = ∑_{k=0}^{n} Bₖ · C_{n-k}`   (a convolution),

and therefore the OGFs multiply:

  **`(B × C)(z) = B(z) · C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` convolution identity
`counts_prod`, proved from `Fintype.card_sigma` / `Fintype.card_prod`. The
generating-function identity `ogf_prod` then follows from `PowerSeries.coeff_mul`
(the Cauchy product) after reconciling the `Finset.antidiagonal` indexing with
the `Fin (n+1)` indexing of the product class.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The Cartesian product `B × C` (F&S §I.2): an object of size `n` is a pair
`(β, γ)` with `|β| + |γ| = n`, enumerated as `Σ k ≤ n, B_k × C_{n-k}`. -/
def CombClass.prod (C D : CombClass) : CombClass where
  Obj n := Σ k : Fin (n + 1), C.Obj k × D.Obj (n - k)
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


