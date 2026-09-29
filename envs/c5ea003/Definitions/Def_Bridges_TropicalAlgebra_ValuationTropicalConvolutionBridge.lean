-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_ValuationTropicalConvolutionBridge
-- name    : Bridges_TropicalAlgebra_ValuationTropicalConvolutionBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:42.36466+00:00
-- url     : https://prove2.me/theorems/4dda58c6-df6c-4783-9004-58f8b70aeb1c
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_ValuationTropicalConvolutionBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.ValuationTropicalConvolutionBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/ValuationTropicalConvolutionBridge.lean by skeleton subtraction
import Mathlib

/-! # Valuation–Tropical Convolution Bridge

This file builds a small, self-contained bridge from additive valuations on a
commutative semiring to a tropical (min-plus) lower bound on the valuations of
finite Cauchy convolutions.

The central statement is `tropConv_le_vprofile_cauchyConv`: the tropical
convolution of two valuation profiles is a pointwise lower bound for the
valuation profile of the Cauchy convolution of the corresponding sequences.
-/

namespace ValuationTropicalConvolutionBridge

open Finset

/-- An additive valuation on a commutative semiring `K`, valued in `WithTop ℕ`. -/
structure AddVal (K : Type*) [CommSemiring K] where
  /-- The underlying valuation map. -/
  v : K → WithTop ℕ
  /-- The valuation of `0` is `⊤`. -/
  map_zero : v 0 = ⊤
  /-- The valuation of `1` is `0`. -/
  map_one : v 1 = 0
  /-- Valuations are additive on products. -/
  map_mul : ∀ x y, v (x * y) = v x + v y
  /-- The valuation of a sum is at least the minimum of the valuations. -/
  min_le_map_add : ∀ x y, min (v x) (v y) ≤ v (x + y)

variable {K : Type*} [CommSemiring K]

/-- The valuation profile of a sequence `a : ℕ → K`. -/
def vprofile (v : AddVal K) (a : ℕ → K) : ℕ → WithTop ℕ := fun n => v.v (a n)

/-- The finite Cauchy convolution of two sequences. -/
def cauchyConv (a b : ℕ → K) (n : ℕ) : K :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- The tropical (min-plus) convolution of two `WithTop ℕ`-valued profiles,
defined as a finite minimum over `range (n+1)`. -/
noncomputable def tropConv (u w : ℕ → WithTop ℕ) (n : ℕ) : WithTop ℕ :=
  (Finset.range (n + 1)).inf' (by simp) (fun k => u k + w (n - k))







end ValuationTropicalConvolutionBridge


