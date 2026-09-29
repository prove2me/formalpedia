-- Prove2me | solution 1 for BorsukUlamArrow.borsuk_ulam_1d
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:48:03.377359+00:00
-- url     : https://prove2.me/submissions/c90be53d-d08f-4244-97d0-1b617d6efb97

-- Sol generated from Novelty/BorsukUlamArrow.lean
import Mathlib
import Definitions.Def_Novelty_BorsukUlamArrow

/-!
# Borsuk–Ulam and Social Choice: the topological kernel and a contrarian disproof

This file investigates the conjecture that **Arrow's impossibility theorem is a
corollary of the Borsuk–Ulam theorem**, and that consequently *"any social choice
function on `n` alternatives is either discontinuous or dictatorial."*

We treat the claim in **contrarian** mode: we isolate the genuine topological
kernel that *is* true, and we **disprove** the over-strong conjecture.

## Part I — The topological kernel (positive results)

The honest mathematical content of the "preference sphere" picture, in the
lowest dimension, is the **one-dimensional Borsuk–Ulam theorem**: a continuous
`2π`-periodic function `f : ℝ → ℝ` (a continuous function on the circle
`S¹ = ℝ / 2πℤ`, i.e. `f : S¹ → ℝ¹`) must send some pair of antipodal points
`x`, `x + π` to the same value.

* `borsuk_ulam_1d` : `∃ x, f x = f (x + π)`.

Its social-choice reading is the genuine kernel of the description's
"contradiction with Pareto efficiency": one cannot continuously and *strictly*
prefer every profile over its antipode.

* `no_strict_antipodal_preference` : `¬ ∀ x, f (x + π) < f x`.
* `no_strict_antipodal_preference'` : `¬ ∀ x, f x < f (x + π)`.

## Part II — The contrarian disproof

The strong conjecture *"continuous ⟹ dictatorial"* is **false** once the space of
preferences is **contractible** (e.g. the real line), rather than a sphere. The
topological obstruction of Borsuk–Ulam/Chichilnisky genuinely requires the
non-contractible sphere topology; it says nothing about aggregation on a convex
domain. We exhibit an explicit **averaging** aggregator on `n ≥ 2` agents that is
simultaneously

* continuous (`avg_continuous`),
* unanimous / Pareto (`avg_unanimity`),
* anonymous, hence symmetric (`avg_anonymous`),
* **non-dictatorial** (`avg_not_dictatorial`),

packaged as `continuous_nondictatorial_aggregator_exists`. This directly refutes
the conjecture that every continuous aggregation rule is dictatorial.
-/

open BorsukUlamArrow

open scoped Real
open Set

/-! ## Part I: one-dimensional Borsuk–Ulam and its social-choice reading -/




/-! ## Part II: contrarian disproof of "continuous ⟹ dictatorial"

We model the space of individual preferences as the real line `ℝ` (a contractible,
convex domain: e.g. positions on a one-dimensional political spectrum). A social
choice / aggregation rule for `n` agents is a map `(Fin n → ℝ) → ℝ`. -/










open BorsukUlamArrow in
theorem solution(f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ x, f (x + 2 * Real.pi) = f x) :
    ∃ x, f x = f (x + Real.pi) := by
  -- Define `g x = f x - f (x + π)`; it is odd under the half-turn: `g (x+π) = -g x`.
  set g : ℝ → ℝ := fun x => f x - f (x + Real.pi);
  -- Hence `g 0 = -g π`, and the IVT on `[0, π]` gives a zero of `g`.
  have h_ivt : ∃ c ∈ Set.Icc 0 Real.pi, g c = 0 := by
    have h_cont : ContinuousOn g (Set.Icc 0 Real.pi) := by
      exact hf.continuousOn.sub ( hf.comp_continuousOn ( continuousOn_id.add continuousOn_const ) )
    have h_ivt : ∃ c ∈ Set.Icc 0 Real.pi, g c = 0 := by
      have h_sign_change : g 0 = -g Real.pi := by
        grind
      have := h_cont.image_Icc Real.pi_pos.le;
      exact this.symm.subset ( Set.mem_Icc.mpr ⟨ by linarith [ Set.mem_Icc.mp ( this ▸ Set.mem_image_of_mem g ( Set.left_mem_Icc.mpr Real.pi_pos.le ) ), Set.mem_Icc.mp ( this ▸ Set.mem_image_of_mem g ( Set.right_mem_Icc.mpr Real.pi_pos.le ) ) ], by linarith [ Set.mem_Icc.mp ( this ▸ Set.mem_image_of_mem g ( Set.left_mem_Icc.mpr Real.pi_pos.le ) ), Set.mem_Icc.mp ( this ▸ Set.mem_image_of_mem g ( Set.right_mem_Icc.mpr Real.pi_pos.le ) ) ] ⟩ );
    exact h_ivt;
  exact h_ivt.imp fun x hx => sub_eq_zero.mp hx.2
