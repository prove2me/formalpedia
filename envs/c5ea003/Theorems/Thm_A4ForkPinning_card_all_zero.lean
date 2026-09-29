-- Prove2me | Theorems.Thm_A4ForkPinning_card_all_zero
-- name    : A4ForkPinning.card_all_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:23:39.761798+00:00
-- url     : https://prove2.me/theorems/73dbdb6d-144c-4cb1-8356-854acd2bdbe1
-- title:
--   The only tuple all of whose entries vanish sits in the fibre over `0`.
-- statement:
--   The only tuple all of whose entries vanish sits in the fibre over `0`.
--
--   ```lean
--   theorem A4ForkPinning.card_all_zero(k : ℕ) (t : ZMod 3) :
--       (univ.filter (fun x : Fin (k + 1) → ZMod 3 => (∑ i, x i = t) ∧ ∀ i, x i = 0)).card
--         = if t = 0 then 1 else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/A4ForkPinning/MultiFactor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/A4ForkPinning/MultiFactor.lean#L58

-- Thm stub generated from Algebra/A4ForkPinning/MultiFactor.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Definitions.Def_Algebra_A4ForkPinning_MultiFactor
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

open A4ForkPinning

open Finset

/-! ## Fibres of the sum map on `(ℤ/3)^{k+1}` -/

theorem A4ForkPinning.card_all_zero(k : ℕ) (t : ZMod 3) :
    (univ.filter (fun x : Fin (k + 1) → ZMod 3 => (∑ i, x i = t) ∧ ∀ i, x i = 0)).card
      = if t = 0 then 1 else 0 := by sorry
