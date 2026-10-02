-- Prove2me | solution 1 for BookSixth.small_displacement_is_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T10:52:13.829012+00:00
-- url     : https://prove2.me/submissions/98abe5c5-a633-4961-a30c-5245ba51e616

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

-- Part 1: the small general lemma.
--
-- A continuous map on a complete metric space whose *displacement* is Lipschitz with
-- constant `q < 1` is a homeomorphism, and its inverse is Lipschitz.
-- This is the analytic core of the Lipschitz-bump ambient-extension construction.
--
-- API notes (all re-read from the pinned revision c5ea003; several earlier line numbers and
-- names in this comment were wrong and are corrected here):
--   * `AntilipschitzWith K f` is a plain `def` (a Prop), NOT a structure, so it is applied to
--     a function rather than built with `constructor`.
--       `AntilipschitzWith.of_le_mul_dist`  Antilipschitz.lean:65  (alias of
--       `antilipschitzWith_iff_le_mul_dist`; from `dist x y ≤ K * dist (f x) (f y)`)
--       `AntilipschitzWith.le_mul_dist`     Antilipschitz.lean:65  (the forward reading)
--       `AntilipschitzWith.injective`       Antilipschitz.lean:94
--       `AntilipschitzWith.to_rightInverse` Antilipschitz.lean:137 (gives `LipschitzWith K g`)
--   * `ContractingWith K f` is likewise a plain `def`:
--       `ContractingWith K f = K < 1 ∧ LipschitzWith K f`  Contracting.lean:40
--       so it is `⟨_, _⟩`, not `constructor`.  On a `Nonempty` `CompleteSpace`:
--       `ContractingWith.fixedPoint`          Contracting.lean:273
--       `ContractingWith.fixedPoint_isFixedPt` Contracting.lean:277, and
--       `IsFixedPt f x` is *defined* as `f x = x` (Logic/Function/Defs.lean:116), so
--       `IsFixedPt.eq` is not a lemma; the equation is `hf.isFixedPt_eq` after
--       `simpa only [IsFixedPt] using hf.fixedPoint_isFixedPt`.
--   * `LipschitzWith.of_dist_le_mul`  Mathlib/Topology/MetricSpace/Lipschitz.lean:50
--   * `Homeomorph.mk`  Mathlib/Topology/Homeomorph/Defs.lean:68
--   * `Real.coe_toNNReal`  Mathlib/Data/NNReal/Defs.lean:151
--   * `NNReal.coe_inv`  Mathlib/Data/NNReal/Defs.lean:208
--   * `CompleteSpace (∀ i, α i)`  Mathlib/Topology/UniformSpace/Pi.lean:105
--   * `Finset.norm_sum_le`  Mathlib/Analysis/Normed/Group/Basic.lean:829
--   * `Finset.sum_le_sum`  Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:108
--   * `norm_neg` is a simp lemma, Mathlib/Analysis/Normed/Group/Basic.lean:69
--   * `Pi.nontrivial`  Mathlib/Logic/Nontrivial/Basic.lean:78

/-- A continuous map `S : Space3 → Space3` whose displacement `S x - x` is Lipschitz with
constant `q < 1` is a homeomorphism.  The map is a bijection, its inverse is continuous, and
`dist (S x) (S y)` is bounded below by `(1 - q) * dist x y`. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q ∧ q < 1) (S : Space3 → Space3)
    (hcont : Continuous S)
    (hlip : ∀ x y : Space3, ‖(S x - x) - (S y - y)‖ ≤ q * ‖x - y‖) :
    ∃ Sinv : Space3 → Space3,
      Continuous Sinv ∧ Function.LeftInverse Sinv S ∧ Function.RightInverse Sinv S ∧
        ∀ x y : Space3, ‖x - y‖ ≤ (1 - q)⁻¹ * ‖S x - S y‖ := by
  classical
  -- `1 - q` is strictly positive, so it is invertible.
  have h1mq : (0 : ℝ) < 1 - q := by linarith
  -- Injectivity and the distance lower bound, packaged as `AntilipschitzWith`.
  -- NOTE the sign: the true identity is
  --     x - y = (S x - S y) - ((S x - x) - (S y - y)),
  -- i.e. the displacement difference is *subtracted*, not added.  Confirmed by
  -- expanding both sides in Z[x, y, S x, S y]; the additive form leaves residual
  -- `2·S x - 2·S y - x + y`.
  have hanti : AntilipschitzWith (1 - q)⁻¹.toNNReal S := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have htri : ‖x - y‖ ≤ ‖S x - S y‖ + ‖(S x - x) - (S y - y)‖ := by
      -- A single step: rewrite `x - y` by the (correct, subtractive) identity, then bound
      -- the difference of norms by the sum.  Splitting this into two steps let `rw [hid]`
      -- close the goal first, so the second step became dead code.
      have hid : (S x - S y) - ((S x - x) - (S y - y)) = x - y := by ring
      -- `hid` orients left-to-right as `difference = x - y`, so the goal must be rewritten
      -- with `← hid`, replacing `x - y` by the difference.  (`rw [hid]` looks for the
      -- difference on the left of the goal and fails.)
      rw [← hid]
      exact norm_sub_le _ _
    have hbound : ‖(S x - x) - (S y - y)‖ ≤ q * ‖x - y‖ := hlip x y
    have hstep : ‖x - y‖ ≤ ‖S x - S y‖ + q * ‖x - y‖ :=
      htri.trans (add_le_add_right hbound (‖S x - S y‖))
    have hmove : (1 - q) * ‖x - y‖ ≤ ‖S x - S y‖ := by linarith
    -- `AntilipschitzWith.of_le_mul_dist` leaves the goal in the form
    --   `dist x y ≤ ↑((1 - q)⁻¹).toNNReal * dist (S x) (S y)`.
    -- `Real.coe_toNNReal` (Data/NNReal/Defs.lean:151) identifies the `ℝ≥0 → ℝ` coercion
    -- of a nonneg real, and `NNReal.coe_inv`/`NNReal.coe_mul` push the product through,
    -- after which `le_div_iff₀` applies to the resulting `d ≤ D / (1 - q)`.
    -- The goal is `‖x - y‖ ≤ ↑((1 - q)⁻¹.toNNReal : ℝ≥0) * ‖S x - S y‖`.
    -- `Real.toNNReal_inv` identifies the base, `NNReal.coe_mul` pushes the product
    -- through, and `NNReal.coe_inv` (Data/NNReal/Defs.lean:208) rewrites
    -- `((r : ℝ≥0)⁻¹ : ℝ)` to `(r : ℝ)⁻¹`.  The intermediate `have` used previously failed
    -- with `LE Type` / `OfNat Type 0` because `(1 - q : ℝ≥0)` was parsed as a type
    -- ascription; doing it as a single rewrite chain avoids that entirely.
    -- Isolate the `NNReal → ℝ` coefficient conversion in a single named hypothesis, so the
    -- conversion is stated once and the main chain does not depend on how the elaborator
    -- happens to display the `NNReal.mk` term.  The coefficient of the goal is
    -- `(↑((1 - q)⁻¹.toNNReal))⁻¹`; `Real.toNNReal_of_nonneg` exposes the base, the
    -- hypothesis-free round trip `Real.coe_toNNReal'` turns it into `max (1 - q)⁻¹ 0`, and
    -- `max_eq_right` — not `max_eq_left`, which would need `(1 - q)⁻¹ ≤ 0` — reduces it.
    -- `↑(NNReal.mk a ha) = a` holds by `rfl` (the `ℝ≥0` structure is a wrapper over `ℝ`),
    -- so the whole `Real.toNNReal_of_nonneg` / `max_eq_right` detour is unnecessary: the
    -- conversion is `NNReal.smul_coe`-free and closes by `rfl`.  The earlier failures came
    -- from `Real.coe_toNNReal'`, which rewrites `↑(Real.toNNReal r)` and so has nothing to
    -- match against the literal `NNReal.mk` the elaborator displays.
    have hinv : (0:ℝ) ≤ (1 - q)⁻¹ := inv_nonneg.mpr h1mq.le
    have hcoef : (((1 - q)⁻¹ : ℝ).toNNReal : ℝ) = (1 - q)⁻¹ := by
      rw [Real.toNNReal_of_nonneg hinv]
      rfl
    -- After `hcoef` the coefficient is already the real `(1 - q)⁻¹`, so the goal is
    -- `‖x - y‖ ≤ (1 - q)⁻¹ * ‖S x - S y‖` and no further `NNReal` lemma applies.
    rw [dist_eq_norm, dist_eq_norm, hcoef]
    -- The goal is `d ≤ D * (1 - q)⁻¹`, a *product* with an inverse, whereas
    -- `le_div_iff₀` is about `d ≤ D / (1 - q)`.  The product is first rewritten to the
    -- quotient by stating the quotient form and closing with `div_eq_mul_inv`, rather than
    -- by rewriting the goal: `rw [← div_eq_mul_inv]` failed because the goal's inverse is
    -- on the *left* factor, `D * (1 - q)⁻¹`, whereas `div_eq_mul_inv` produces `D / (1 - q)`
    -- with the division on the right.
    -- `le_div_iff₀ : 0 < c → (a ≤ b / c ↔ a * c ≤ b)`, so its `.mpr` direction wants the
    -- scalar on the *right* of `a`, while `hmove` has it on the left.  Over the reals the two
    -- agree, so the hypothesis is normalised once by commutativity.
    have hmove' : ‖x - y‖ * (1 - q) ≤ ‖S x - S y‖ := by simpa [mul_comm] using hmove
    have hdiv : ‖x - y‖ ≤ ‖S x - S y‖ / (1 - q) := (le_div_iff₀ h1mq).2 hmove'
    -- `div_eq_mul_inv` gives `D / (1 - q) = D * (1 - q)⁻¹`, but the goal has the inverse on
    -- the left, `(1 - q)⁻¹ * D`.  These agree by commutativity, so `simpa [mul_comm]`.
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  -- Surjectivity.  For a fixed target `x`, the map `F y = x - (S y - y)` is a contraction
  -- with constant exactly `q` in `y`, so it has a fixed point `y`; then
  -- `x - (S y - y) = y`, i.e. `S y = x`.
  letI : CompleteSpace Space3 := inferInstance
  letI : Nonempty Space3 := inferInstance
  have hsurj : ∀ x : Space3, ∃ y : Space3, S y = x := by
    intro x
    -- The contraction `F y = x - (S y - y)`.
    have hcontra : ContractingWith q.toNNReal (fun y : Space3 => x - (S y - y)) := by
      refine ⟨?_, ?_⟩
      · -- `ContractingWith K f` is `K < 1 ∧ LipschitzWith K f` with `K : ℝ≥0`, so the goal
        -- here is `q.toNNReal < (1 : ℝ≥0)`.  The exact lemma is
        -- `NNReal.coe_lt_coe : (r₁ : ℝ) < r₂ ↔ r₁ < r₂` (Data/NNReal/Defs.lean:325), i.e.
        -- it is oriented *from* the `ℝ` statement, so the goal is closed by `.mpr` after the
        -- base has been displayed as `↑q`.  `Real.toNNReal_of_nonneg` does that display.
        rw [Real.toNNReal_of_nonneg hq.1]
        exact NNReal.coe_lt_coe.mpr hq.2
      · -- Build the `LipschitzWith` half in its `dist` form, which is what `hlip` speaks.
        -- `LipschitzWith.of_dist_le_mul` (Lipschitz.lean:50) bridges to the `edist`-form
        -- goal, so no `edist` rewriting is needed here.
        refine LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_
        -- `(x - E y₁) - (x - E y₂) = -(E y₁ - E y₂)`, so the constant is exactly `q`.
        have hid : (x - (S y₁ - y₁)) - (x - (S y₂ - y₂))
            = -((S y₁ - y₁) - (S y₂ - y₂)) := by ring
        -- The coefficient is `((q : ℝ≥0) : ℝ)`, i.e. the coercion of a literal `NNReal.mk`;
        -- it is normalised by the same round trip under `0 ≤ q`.
        have hcoefq : ((q : ℝ).toNNReal : ℝ) = q := by
          rw [Real.toNNReal_of_nonneg hq.1]
          rfl
        -- `hlip` is already in `‖-‖` form.  A `calc` is used rather than rewriting the
        -- goal with `← norm_neg, ← hid`: those fire in the wrong direction (the goal after
        -- `← norm_neg` is `‖-(x - … - (x - …))‖ ≤ …`, so `← hid` looks for
        -- the *negated* form of `hid` and finds nothing).
        rw [dist_eq_norm, dist_eq_norm, hcoefq]
        calc ‖x - (S y₁ - y₁) - (x - (S y₂ - y₂))‖
            = ‖-((S y₁ - y₁) - (S y₂ - y₂))‖ := by rw [hid]
          _ = ‖(S y₁ - y₁) - (S y₂ - y₂)‖ := norm_neg _
          _ ≤ q * ‖y₁ - y₂‖ := hlip y₁ y₂
    have hfix := hcontra.fixedPoint_isFixedPt
    -- `IsFixedPt f y` is *defined* as `f y = y` (Logic/Function/Defs.lean:116), so `hfix`
    -- is the fixed-point equation for the unnamed `hcontra.fixedPoint`.  Prove the
    -- rearrangement for that exact term first, then discharge the existential; this avoids
    -- introducing a `let`-bound `y` whose definitional unfolding the goal does not share.
    have hid : x - (S (hcontra.fixedPoint : Space3) - hcontra.fixedPoint)
        = hcontra.fixedPoint := hfix
    refine ⟨hcontra.fixedPoint, ?_⟩
    -- `x - (S f - f) = f` rearranges to `S f = x`, by cancellation in the additive group:
    --   `x + (f + -(S f)) = 0 + f  ⟹  x + -(S f) = 0  ⟹  x - S f = 0  ⟹  x = S f`.
    -- `linarith` is unusable here: `Space3` is a Pi type over `ℝ`, not one `ℝ`-linear
    -- expression, and it was left with the bare goal `False`.
    have hE : S (hcontra.fixedPoint : Space3) = x := by
      -- `hid : x - (S f - f) = f` is one equation in the additive commutative group `Space3`.
      -- Two earlier attempts normalised it with `simp` and then cancelled, and both fail as
      -- tactics rather than as mathematics:
      --   * a bare `simpa` containing `add_comm` rewrites the *whole* goal, collapsing the
      --     intended intermediate into the final statement, so the cancellation step that
      --     follows is left with no goal;
      --   * `simpa only [sub_eq_add_neg, add_assoc, add_comm, zero_add]` leaves a residual
      --     difference, because the hypothesis normalises to `x + -(S f + -f) = f`, and
      --     pushing that negation *through* the inner subtraction needs a rewrite the default
      --     simp set will not apply in that direction.
      -- The repair appends `-f` to both sides and lets `abel` cancel.  `abel` evaluates both
      -- sides of an equation in a commutative additive group to a canonical form
      -- (Mathlib/Tactic/Abel.lean rewrites `HSub.hSub` into `HAdd` with a `Neg.neg` and
      -- recurses through `Neg.neg`), so the rearrangement becomes
      --     x - S f = ((x - S f) + f) - f = (x - (S f - f)) - f = f - f = 0.
      -- The two `abel` steps are closed group identities that do not mention `hid`; the third
      -- step is `hid` itself.  No `simp` set is involved, so there is no over-normalisation.
      have h3 : x - S (hcontra.fixedPoint : Space3) = 0 := by
        calc x - S (hcontra.fixedPoint : Space3)
            = ((x - S (hcontra.fixedPoint : Space3)) + hcontra.fixedPoint)
                - hcontra.fixedPoint := by abel
          _ = (x - (S (hcontra.fixedPoint : Space3) - hcontra.fixedPoint))
              - hcontra.fixedPoint := by abel
          _ = hcontra.fixedPoint - hcontra.fixedPoint := by rw [hid]
          _ = 0 := sub_self _
      -- `sub_eq_zero.mp : a - b = 0 → a = b` yields `x = S f`; the goal is the reverse
      -- orientation, so `.symm` is applied, as at Analysis/InnerProductSpace/Dual.lean:166.
      exact (sub_eq_zero.mp h3).symm
    exact hE
  -- `hsurj : ∀ x, ∃ y, S y = x` is a `∀`, not an existential, so it must be *applied* to
  -- the point being inverted; destructuring it directly fails with
  -- "Tactic `rcases` failed: ... is not an inductive datatype".
  let Sinv : Space3 → Space3 := fun x => (hsurj x).choose
  have hSinv : Function.RightInverse Sinv S := fun x => (hsurj x).choose_spec
  refine ⟨Sinv, ?_, ?_, ?_, ?_⟩
  · -- `Sinv` is `LipschitzWith (1-q)⁻¹` by `AntilipschitzWith.to_rightInverse`, hence continuous.
    have hli : LipschitzWith (1 - q)⁻¹.toNNReal Sinv := hanti.to_rightInverse hSinv
    exact hli.continuous
  · intro x
    -- The goal is `Function.LeftInverse Sinv S`, i.e. `Sinv (S x) = x`.  `hSinv` states
    -- `S (Sinv y) = y`, which is the *other* obligation, so it is used one bullet later.
    -- Injectivity of `S` bridges the two: `hSinv (S x)` is `S (Sinv (S x)) = S x`, so
    -- injectivity gives `Sinv (S x) = x` directly.  No `.symm`: the hypothesis must have
    -- the form `S a = S b`, and `hSinv (S x)` already does.
    exact hanti.injective (hSinv (S x))
  · intro x
    -- The goal is `Function.RightInverse Sinv S`, i.e. `S (Sinv x) = x`, which is exactly
    -- the `hSinv` produced from surjectivity.
    exact hSinv x
  · intro x y
    -- `AntilipschitzWith.le_mul_dist` is stated with `dist`, while the goal is already in
    -- `‖-‖` form with an `ℝ` coefficient, so the `rw [dist_eq_norm]` that previously sat
    -- here had nothing to match ("Did not find an occurrence of the pattern dist ?a ?b").
    -- `hanti`'s own coercion is `↑((1 - q)⁻¹.toNNReal : ℝ≥0)`, which `Real.coe_toNNReal'`
    -- and `max_eq_right` reduce to `(1 - q)⁻¹`.  Two facts were previously wrong here:
    -- the lemma is `max_eq_right : b ≤ a → max a b = b`, not `max_eq_left`, because the
    -- `0` is on the *right* of `max (1 - q)⁻¹ 0`; and the sign argument is
    -- `inv_nonneg.mpr h1mq.le`, i.e. `0 ≤ (1 - q)⁻¹`, not `h1mq.le : 0 ≤ 1 - q`.
    -- `max_eq_left` would need `(1 - q)⁻¹ ≤ 0`, which is false, so it could never fire —
    -- that is what produced the repeated "`simp` made no progress".
    have hlow := hanti.le_mul_dist x y
    -- `hlow` is in `dist` form, the goal in `‖-‖` form, and its coefficient is the same
    -- `NNReal → ℝ` conversion as in the antilipschitz bound.
    have hcoef : (((1 - q)⁻¹ : ℝ).toNNReal : ℝ) = (1 - q)⁻¹ := by
      rw [Real.toNNReal_of_nonneg (inv_nonneg.mpr h1mq.le)]
      rfl
    rw [dist_eq_norm, dist_eq_norm, hcoef] at hlow
    exact hlow
