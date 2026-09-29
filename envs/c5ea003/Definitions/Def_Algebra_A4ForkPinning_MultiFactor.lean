-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_MultiFactor
-- name    : Algebra_A4ForkPinning_MultiFactor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:06:10.865376+00:00
-- url     : https://prove2.me/theorems/7ea7edab-e5a8-4d7a-beff-29a90442bfac
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_MultiFactor
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.MultiFactor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/MultiFactor.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Definitions.Def_Algebra_A4ForkPinning_Semiprime
/-
# The order-3 channel for `k` factors, and its collapse

The semiprime laws of `Semiprime.lean` are the case `k = 2` of a family.  Let
`N = p₁⋯p_{k+1}` be a product of `k+1` unramified primes of the `A₄`-field; the
dial `N mod 9` sees only the sum `s = Σ chi9(pᵢ) ∈ ℤ/3` of the cube classes.

* `A4ForkPinning.card_fiber_sum` — every fibre of the sum map
  `(ℤ/3)^{k+1} → ℤ/3` has exactly `3^k` points (proved by an explicit bijection);
* `A4ForkPinning.allSplitRate_eq_count` — hence `P(all factors split | s) = 3^{-k}`
  if `s = 0` and `0` otherwise: the "all split" fork is the `3^{-k}`-thinning of
  the pinned fork `[s = 0]`;
* `A4ForkPinning.info_all_split` — **the `k`-factor AND law**
  `I = H(3^{-(k+1)}) - (1/3)·H(3^{-k})`, generalising the semiprime value
  `H(1/9) - (1/3)H(1/3)`;
* `A4ForkPinning.info_all_split_strict` — it is a genuine leak: `0 < I < H(F)`;
* `A4ForkPinning.info_all_split_tendsto_zero` — **the channel collapses**:
  `I → 0` as the number of factors grows.  Quantitatively, the residue of a
  many-factor number tells one essentially nothing about its factors' splitting
  behaviour: the "factor-uselessness" of the pinned fork.
-/

namespace A4ForkPinning

open Finset

/-! ## Fibres of the sum map on `(ℤ/3)^{k+1}` -/



/-! ## The `k`-factor AND channel -/

/-- Conditional probability that **all** `k+1` factors split, given the class of `N`. -/
noncomputable def allSplitRate (k : ℕ) : Fin 3 → ℝ :=
  fun i => (1 / 3 : ℝ) ^ k * (![1, 0, 0] : Fin 3 → ℝ) i






/-! ## Collapse of the channel -/




end A4ForkPinning


