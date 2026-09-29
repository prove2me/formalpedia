-- Prove2me | solution 1 for ECAFixedVariety.shift_one_of_period_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:13:26.303674+00:00
-- url     : https://prove2.me/submissions/0ed8d788-dccb-419d-a20c-e146d1bf712d

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

/-- Iterating shift-by-`p` invariance. -/
lemma iterate_period {n p : ℕ} {s : Cfg n} (h : ∀ i, s (i + (p : ZMod n)) = s i) :
    ∀ (k : ℕ) (i : ZMod n), s (i + (p : ZMod n) * (k : ZMod n)) = s i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ m ih =>
      intro i
      have hstep : i + (p : ZMod n) * ((m + 1 : ℕ) : ZMod n)
          = (i + (p : ZMod n) * (m : ZMod n)) + (p : ZMod n) := by
        push_cast
        ring
      rw [hstep, h, ih]

























open ECAFixedVariety in
theorem solution{n p : ℕ} (hn : n ≠ 0) (hcop : Nat.Coprime p n) {s : Cfg n}
    (h : ∀ i, s (i + (p : ZMod n)) = s i) : ∀ i, s (i + 1) = s i := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 ((ZMod.isUnit_iff_coprime p n).2 hcop)
  intro i
  have hcast : ((p : ℕ) : ZMod n) * ((v.val : ℕ) : ZMod n) = 1 := by
    simpa [ZMod.natCast_val, ZMod.cast_id] using hv
  have hiter := iterate_period h v.val i
  rwa [hcast] at hiter
