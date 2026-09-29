-- Prove2me | Definitions.Def_Novelty_ECAFixedVarietyCore
-- name    : Novelty_ECAFixedVarietyCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:16:32.924965+00:00
-- url     : https://prove2.me/theorems/b76e2998-d734-4c38-b75c-841e7fbf96af
-- title:
--   Aether Catalog definitions — Novelty_ECAFixedVarietyCore
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ECAFixedVarietyCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ECAFixedVarietyCore.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_CellularAutomataAlgebraicGeometry

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

namespace ECAFixedVariety

open CellularAutomataAlgebraicGeometry

/-- Cyclic configuration space of size `n`: a point of affine `n`-space over `𝔽₂`.
For `n = 0` this is the bi-infinite configuration space `ℤ → 𝔽₂`. -/
abbrev Cfg (n : ℕ) := ZMod n → ZMod 2

/-- The `𝔽₂`-valued local rule of Wolfram rule number `rule`. -/
def localRuleZ (rule : ℕ) (l c r : ZMod 2) : ZMod 2 :=
  if rule.testBit (4 * l.val + 2 * c.val + r.val) then 1 else 0


/-- Boolean-to-`𝔽₂` encoding of a cell. -/
def ofBool (b : Bool) : ZMod 2 := cond b 1 0




/-- One synchronous update step of Wolfram rule `rule` on cyclic configurations. -/
def step (rule : ℕ) {n : ℕ} (s : Cfg n) : Cfg n :=
  fun i => localRuleZ rule (s (i - 1)) (s i) (s (i + 1))

/-- The fixed-point variety `V(f) = {s : f(s) = s}` of a Wolfram rule. -/
def fixedSet (rule n : ℕ) : Set (Cfg n) := {s | step rule s = s}



/-! ### Periodicity transfer on the ring

Many fixed-point loci are governed by a spatial period `p`; when `p` is
invertible modulo the ring size the configuration is forced to be constant.
These generic lemmas are used for `p = 2` and `p = 3` below. -/





/-- A rule is *additive* when its local rule is `𝔽₂`-linear in the three
arguments; these are exactly the rules whose fixed-point locus is a linear
subvariety. -/
def IsAdditive (rule : ℕ) : Prop :=
  ∀ l c r l' c' r' : ZMod 2,
    localRuleZ rule (l + l') (c + c') (r + r') =
      localRuleZ rule l c r + localRuleZ rule l' c' r'



/-- `V(rule, n)` *has dimension* `d` when it is a linear subvariety of affine
`n`-space of `𝔽₂`-dimension `d`. -/
def HasFixedDim (rule n d : ℕ) : Prop :=
  ∃ W : Submodule (ZMod 2) (Cfg n),
    (W : Set (Cfg n)) = fixedSet rule n ∧ Module.finrank (ZMod 2) W = d


/-- Evaluation of a configuration at the two seed cells `0` and `1`. -/
def seedPair (n : ℕ) : Cfg n →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun s := ![s 0, s 1]
  map_add' a b := by
    funext j
    fin_cases j <;> simp
  map_smul' c a := by
    funext j
    fin_cases j <;> simp



section Rule204





end Rule204

section Rule0





end Rule0

end ECAFixedVariety


