-- Prove2me | solution 1 for BookSixth.small_displacement_is_homeomorph_div
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-26T12:15:52.142799+00:00
-- url     : https://prove2.me/submissions/6cdf5f1a-f186-47e4-b2bd-7101504460fe

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- **Disproof of `BookSixth.small_displacement_is_homeomorph_div`.**

The target asks for the conclusion

    ∀ x y : Space3, (1 - q) * ‖S x - S y‖ ≥ ‖x - y‖

under the hypotheses `hq : 0 ≤ q ∧ q < 1` and
`hlip : ∀ x y : Space3, ‖(S x - x) - (S y - y)‖ ≤ q * ‖x - y‖`.

That inequality is strictly stronger than the true bound, which is
`‖x - y‖ ≤ (1 - q)⁻¹ * ‖S x - S y‖`, equivalently `‖S x - S y‖ ≥ (1 - q) * ‖x - y‖`.
The target asks instead for `‖S x - S y‖ ≥ (1 - q)⁻¹ * ‖x - y‖`, which is stronger by the
factor `(1 - q)² < 1` whenever `0 < q < 1`.

The counterexample is the uniform contraction `S x = (1/2) • x` at `q = 1/2`:

* `hq` holds, since `0 ≤ 1/2 < 1`.
* `S` is continuous, being `(1/2)⁻¹`-scaled identity, i.e. `LinearMap.id` followed by `smul`.
* the displacement is `S x - x = -(1/2) • x`, so the displacement difference is
  `-(1/2) • (x - y)` with norm `(1/2) * ‖x - y‖`, and `hlip` holds with `q = 1/2`;
* but at `x = 0` and `y = ![1, 0, 0]` the conclusion reads
  `(1 - 1/2) * ‖S 0 - S ![1,0,0]‖ = (1/2) * (1/2) = 1/4 ≥ 1 = ‖0 - ![1,0,0]‖`, which is false.

The natural-language statement agrees with the *Proved* sibling
`BookSixth.small_displacement_is_homeomorph` (target `5f342cbf`, Proved as candidate 3304) and
not with this formal statement: "moves no two points closer together by more than a factor
`1 - q`" is the weaker, correct `‖S x - S y‖ ≥ (1 - q) * ‖x - y‖`. -/
theorem solution
    : ¬ (∀ (q : ℝ) (hq : 0 ≤ q ∧ q < 1) (S : Space3 → Space3)
      (hcont : Continuous S)
      (hlip : ∀ x y : Space3, ‖(S x - x) - (S y - y)‖ ≤ q * ‖x - y‖),
      ∃ Sinv : Space3 → Space3,
        Continuous Sinv ∧ Function.LeftInverse Sinv S ∧ Function.RightInverse Sinv S ∧
          ∀ x y : Space3, (1 - q) * ‖S x - S y‖ ≥ ‖x - y‖) := by
  -- The counterexample is the uniform contraction by `1/2`, at `q = 1/2`.
  intro h
  -- `S x = (1/2) • x` is a continuous linear map, so it is in particular continuous.
  have hScont : Continuous (fun x : Space3 => (2 : ℝ)⁻¹ • x) := by
    fun_prop
  -- The displacement bound `hlip` for `S = fun x => (1/2) • x`.  The displacement difference
  -- is `-(1/2) • (x - y)`, by `module`, so its norm is `(1/2) * ‖x - y‖` after `norm_neg`
  -- and `smul_eq_mul`, and `hlip` holds with `q = 1/2` by reflexivity.
  have hlip' : ∀ x y : Space3,
      ‖(((2 : ℝ)⁻¹ • x) - x) - ((2 : ℝ)⁻¹ • y - y)‖ ≤ (2 : ℝ)⁻¹ * ‖x - y‖ := by
    intro x y
    have hkey : ((2 : ℝ)⁻¹ • x - x) - ((2 : ℝ)⁻¹ • y - y)
        = -((2 : ℝ)⁻¹ • (x - y)) := by
      module
    -- After `hkey` and `norm_neg` the goal is `‖2⁻¹ • (x - y)‖ ≤ 2⁻¹ * ‖x - y‖`, and
    -- `norm_smul : ‖a • v‖ = ‖a‖ * ‖v‖` reduces the left side to `‖2⁻¹‖ * ‖x - y‖`.  For a real
    -- scalar `‖2⁻¹‖` is *definitionally* `2⁻¹` — `Real.norm_eq_abs` followed by `abs_of_pos` —
    -- so the goal is already reflexivity and no `abs_of_nonneg` rewrite belongs here: an
    -- earlier candidate appended one and it found no `|?m|` subterm to match, because
    -- `norm_smul` had already reduced the absolute value away.
    rw [hkey, norm_neg, norm_smul]
    -- The goal is now `2⁻¹ * ‖x - y‖ ≤ 2⁻¹ * ‖x - y‖`.
    -- The coercion is annotated because `le_rfl` needs a `Preorder`, and after `norm_smul`
    -- the metavariable for the normed group is not determined by the goal alone; an earlier
    -- candidate left it open and got `typeclass instance problem is stuck, Preorder ?m`.
    -- `norm_of_nonneg` lives in `namespace Real` (Mathlib/Analysis/Normed/Group/Real.lean:62),
    -- so the bare name is an `Unknown identifier`; `Real.norm_of_nonneg` is the correct one.
    have hnn : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr (by norm_num))
    rw [hnn]
  -- `h` is instantiated at `q = 1/2` and `S = fun x => (1/2) • x`.  Only the last conjunct of
  -- the resulting existential is needed, so it is taken as a hypothesis and refuted at the
  -- concrete pair `x = 0`, `y = ![1, 0, 0]`, where it reads `1/4 ≥ 1`.
  have hExist : ∃ Sinv : Space3 → Space3,
      Continuous Sinv ∧ Function.LeftInverse Sinv (fun x : Space3 => (2 : ℝ)⁻¹ • x) ∧
        Function.RightInverse Sinv (fun x : Space3 => (2 : ℝ)⁻¹ • x) ∧
        ∀ x y : Space3, (1 - (2 : ℝ)⁻¹)
          * ‖((2 : ℝ)⁻¹ • x) - ((2 : ℝ)⁻¹ • y)‖ ≥ ‖x - y‖ :=
    h (2 : ℝ)⁻¹ ⟨by norm_num, by norm_num⟩ _ hScont hlip'
  obtain ⟨Sinv, _, _, _, hbound⟩ := hExist
  -- The conclusion is refuted at `x = 0`, `y = ![1, 0, 0]`.  The smul difference is combined
  -- by `module` and `0 - ![1,0,0]` is `-![1,0,0]` by `simp`, so the instantiated hypothesis
  -- becomes
  --     (1 - 1/2) * ‖(1/2) • -![1, 0, 0]‖ ≥ ‖![1, 0, 0]‖
  --     ⟷ (1/2) * ((1/2) * ‖![1, 0, 0]‖) ≥ ‖![1, 0, 0]‖
  --     ⟷ (1/4) * n ≥ n   for   n := ‖![1, 0, 0]‖.
  -- Only `n > 0` is needed to refute this — a positive number scaled by `1/4 < 1` is strictly
  -- smaller than itself — so the *value* of the supremum norm of `![1, 0, 0]` is never
  -- computed.  That matters because `Space3 = Fin 3 → ℝ` carries the supremum norm: there is no
  -- `Inner` instance, so `PiLp.norm_eq_sqrt_inner` is an `Unknown constant` here, and the
  -- `Finset.univ.sup` that `Pi.norm_def` produces neither reduces under `simp` nor lets
  -- `Finset.sup_le`'s bound metavariable be determined (`OrderBot ?m`).  Six successive
  -- candidates failed on that single value; not needing it removes the whole class of problem.
  have hbad := hbound (0 : Space3) (![1, 0, 0] : Space3)
  have hsmul : ((2 : ℝ)⁻¹ • (0 : Space3)) - ((2 : ℝ)⁻¹ • (![1, 0, 0] : Space3))
      = (2 : ℝ)⁻¹ • ((0 : Space3) - ![1, 0, 0]) := by module
  rw [hsmul] at hbad
  have hzero : (0 : Space3) - ![1, 0, 0] = -![1, 0, 0] := by simp
  rw [hzero, norm_neg] at hbad
  -- `Real.norm_eq_abs` is `@[simp]` (Mathlib/Analysis/Normed/Group/Real.lean:55) and
  -- `abs_of_pos` settles `|2⁻¹|`, so `simp` alone reduces the smul norm; the scalar
  -- arithmetic is then closed by `norm_num`, leaving `(1/4) * n ≥ n` with `n` treated as an atom.
  have hpos2 : (0:ℝ) < (2 : ℝ)⁻¹ := by norm_num
  -- `simp only [norm_smul, abs_of_pos hpos2, smul_eq_mul]` rewrites the *first* `‖2⁻¹ • _‖` it
  -- meets and leaves the second as `‖-![1, 0, 0]‖`, so the two norms are never identified and
  -- `nlinarith` cannot see that `hbad` reads `n ≤ 1/2 * (1/2 * n)`.  The remote diagnostic for
  -- candidate 3359 shows exactly that residual goal:
  --     hbad : ‖![1, 0, 0]‖ ≤ 1/2 * (1/2 * ‖-![1, 0, 0]‖)
  -- Adding `norm_neg` to the same `simp only` list closes the inner negation as well, after
  -- which `hbad` is `n ≤ 1/2 * (1/2 * n)` and `nlinarith` refutes it from `n > 0`.
  simp only [norm_smul, norm_neg, abs_of_pos hpos2, smul_eq_mul] at hbad
  norm_num at hbad
  -- `hbad : (1/4) * ‖![1, 0, 0]‖ ≥ ‖![1, 0, 0]‖`.  The vector is nonzero — evaluating a
  -- proposed equality at the coordinate `0` refutes it — so `norm_pos_iff.mpr` gives strict
  -- positivity, and `nlinarith` closes the contradiction.
  have hne : (![1, 0, 0] : Space3) ≠ 0 := by
    intro hz
    have hz0 := congr_fun hz (0 : Fin 3)
    simp at hz0
  have hpos : (0:ℝ) < ‖(![1, 0, 0] : Space3)‖ := norm_pos_iff.mpr hne
  nlinarith [hpos]
