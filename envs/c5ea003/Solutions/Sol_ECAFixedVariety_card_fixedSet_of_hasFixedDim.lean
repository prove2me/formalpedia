-- Prove2me | solution 1 for ECAFixedVariety.card_fixedSet_of_hasFixedDim
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:52:25.766586+00:00
-- url     : https://prove2.me/submissions/0a89adbf-41fb-4bb6-93be-5247794dcfe1

-- Sol generated from Novelty/ECAFixedVarietyCore.lean
import Mathlib
import Definitions.Def_Novelty_CellularAutomataAlgebraicGeometry
import Definitions.Def_Novelty_ECAFixedVarietyCore

/-!
# The fixed-point variety of an elementary cellular automaton

This file sets up the algebraic-geometry style framework in which the
"ECA complexity = dimension of the fixed-point variety" conjecture can be
*tested*, building directly on the Boolean local rules of
`Novelty.CellularAutomataAlgebraicGeometry`.

A cyclic configuration of size `n` is a function `ZMod n → ZMod 2`, i.e. a point
of the affine space `𝔸ⁿ_{𝔽₂}` (for `n = 0` this degenerates to the bi-infinite
configuration space `ℤ → ZMod 2`, which is why all statements below are stated
uniformly over `ZMod n`).  The *fixed-point variety* of Wolfram rule `rule` is

  `V(rule, n) = { s : ZMod n → ZMod 2 | step rule s = s }`,

the `𝔽₂`-points of the zero locus of the `n` cubic polynomials
`fᵣ(s_{i-1}, s_i, s_{i+1}) - s_i`.

## Main results

* `localRuleZ_ofBool` — the `ZMod 2`-valued local rule agrees with the Boolean
  local rule of the catalog file, so this is genuinely the same dynamics.
* `mem_fixedSet_iff` — pointwise description of the fixed-point variety.
* `fixedSet_rotate` — the variety is invariant under the shift, i.e. it is a
  cyclic subshift of finite type, not an arbitrary subset.
* `IsAdditive.fixedSubmodule` — for an *additive* rule the variety really is a
  linear subspace, so a dimension `HasFixedDim` is defined.
* `rule204_hasFixedDim`, `rule204_fixedSet_univ` — the identity rule (Wolfram
  class 1/2) attains the maximal dimension `n`.
* `rule0_hasFixedDim_zero` — the null rule has dimension `0`.
* `hasFixedDim_unique` — the dimension, when it exists, is well defined.
-/

open ECAFixedVariety

open CellularAutomataAlgebraicGeometry












/-! ### Periodicity transfer on the ring

Many fixed-point loci are governed by a spatial period `p`; when `p` is
invertible modulo the ring size the configuration is forced to be constant.
These generic lemmas are used for `p = 2` and `p = 3` below. -/


























open ECAFixedVariety in
theorem solution{rule n d : ℕ} [NeZero n] (h : HasFixedDim rule n d) :
    Nat.card (fixedSet rule n) = 2 ^ d := by
  obtain ⟨W, hW, hd⟩ := h
  haveI : Fintype W := Fintype.ofFinite _
  have hcard : Fintype.card W = 2 ^ d := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
    simpa [hd, ZMod.card] using this
  have hco : Nat.card ((W : Set (Cfg n))) = Nat.card W := rfl
  rw [← hW, hco, Nat.card_eq_fintype_card, hcard]
