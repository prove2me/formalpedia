-- Prove2me | Definitions.Def_Novelty_SYZOuterClass
-- name    : Novelty_SYZOuterClass
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:31.836032+00:00
-- url     : https://prove2.me/theorems/845a4929-cb80-46dc-b0a0-c59201365d89
-- title:
--   Aether Catalog definitions — Novelty_SYZOuterClass
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SYZOuterClass`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SYZOuterClass.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_SYZDualityRankN
import Definitions.Def_Novelty_SYZMonodromyDuality

/-!
# Arithmetic Mirror Symmetry X — the outer class of integral SYZ T-duality

This file is the third part of cycle 4 of the research thread.  It closes **Conjecture G** of
`FUTURE_DIRECTIONS.md`: the fiberwise dualization `δ : M ↦ (M⁻¹)ᵀ` of the integral monodromy
group `GL_n(ℤ)` is an involutive automorphism whose class in the outer automorphism group
has order **exactly two** for every `n ≥ 2`, and is trivial for `n ≤ 1`.

Cycle 1 supplied involutivity (`dualMon_involutive`, `dualRep_dualRep`) and cycle 2 supplied
the non-innerness dichotomy (`dualMon_inner_iff_rank_le_one`).  What is added here is the
group-theoretic packaging that turns those two facts into a statement about
`Out(GL_n(ℤ)) = Aut / Inn`: the inner automorphisms are shown to be a normal subgroup of
`MulAut`, the quotient is formed, and the order of the T-duality class is computed.

## Main results

* `innerAut_normal` — the inner automorphisms `MulAut.conj.range` form a normal subgroup of
  `MulAut G`, for any group `G` (the conjugation formula `f ∘ conj g ∘ f⁻¹ = conj (f g)`).
* `OuterAut` — the outer automorphism group `MulAut G ⧸ MulAut.conj.range`.
* `dualEquiv_mul_self` — `δ² = 1` in `MulAut (GL_n(ℤ))`, the group-level form of cycle 1's
  double-dual theorem.
* `dualEquiv_mem_inner_iff` — `δ` is inner **iff** `n ≤ 1`, transported from
  `dualMon_inner_iff_rank_le_one`.
* `tDualityClass` — the class `[δ] ∈ Out(GL_n(ℤ))`.
* `tDualityClass_orderOf_eq_two` — **Conjecture G**: `order [δ] = 2` for every `n ≥ 2`.
* `tDualityClass_eq_one_iff`, `tDualityClass_orderOf_eq_two_iff` — the full dichotomy:
  `[δ] = 1 ↔ n ≤ 1` and `order [δ] = 2 ↔ 2 ≤ n`.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  Cycle 2 proved "`δ` is inner iff `n ≤ 1`", which is a
  statement about a *single* automorphism.  The intrinsic statement should be about its
  class in `Out`: since `δ² = id`, the class is `2`-torsion, so its order is `1` or `2`, and
  non-innerness picks out `2`.  Guess: `order [δ] = 2` exactly when `n ≥ 2`, with no
  exceptional ranks — the order is a *complete* invariant of the dichotomy.
* **Experiment (Experimenter).**  Mathlib has `MulAut.conj : G →* MulAut G` but no
  normality instance for its range and no `Out`, so both had to be built.  Normality is the
  one-line conjugation identity `f (conj g) f⁻¹ = conj (f g)`, checked by `ext` and `simp`
  with `MulAut.mul_apply`.  With the quotient in place, `orderOf_eq_prime` at `p = 2`
  reduces the theorem to exactly the two inputs from cycles 1 and 2.
* **Analysis (Analyst).**  The order-two statement is strictly stronger than
  non-innerness: it says the T-duality class *generates a `ℤ/2`* in `Out`, so no power of
  `δ` other than `δ` itself is a new outer symmetry, and composing `δ` with any change of
  basis can never produce an automorphism of infinite order.  Combined with cycle 2's trace
  obstruction being stable under block embedding, the `ℤ/2` is uniform in the rank.
* **Critique (Critic).**  Nothing is definitional here: `orderOf_eq_prime` needs both
  `x² = 1` (cycle 1) and `x ≠ 1` (cycle 2), and dropping either gives a false statement
  (`n ≤ 1` really does give order `1`, which is proved as the companion
  `tDualityClass_eq_one_iff`).  No `decide`, no `native_decide`.
* **Synthesis (PI).**  Integral SYZ T-duality is a canonical `ℤ/2 ⊆ Out(GL_n(ℤ))` for every
  `n ≥ 2`, and the mirror involution on local systems is the corresponding outer symmetry.
-/

namespace Novelty.MirrorBridge

open Matrix

section Outer

variable (G : Type*) [Group G]

/-- **Inner automorphisms are normal.**  For `f ∈ Aut G` and `g ∈ G`,
`f ∘ conj g ∘ f⁻¹ = conj (f g)`. -/
instance innerAut_normal : (MulAut.conj (G := G)).range.Normal := by
  constructor
  rintro n ⟨g, rfl⟩ f
  refine ⟨f g, ?_⟩
  ext x
  simp [MulAut.mul_apply, MulAut.conj]

/-- The **outer automorphism group** `Out G = Aut G / Inn G`. -/
abbrev OuterAut : Type _ := MulAut G ⧸ (MulAut.conj (G := G)).range

variable {G}



end Outer

section TDuality

variable {n : ℕ}



/-- The **class of integral SYZ T-duality** in `Out(GL_n(ℤ))`. -/
def tDualityClass (n : ℕ) : OuterAut (IntGL n) :=
  QuotientGroup.mk (dualEquiv : MulAut (IntGL n))






end TDuality

end Novelty.MirrorBridge


