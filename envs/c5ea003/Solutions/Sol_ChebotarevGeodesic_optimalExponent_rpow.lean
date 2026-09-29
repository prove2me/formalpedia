-- Prove2me | solution 1 for ChebotarevGeodesic.optimalExponent_rpow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:01:25.045135+00:00
-- url     : https://prove2.me/submissions/b24e4585-ffc8-4d1d-982a-ab6c5fb87e4c

-- Sol generated from Shared/ChebotarevGeodesicOptimal.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_optimalExponent
import Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_of_growth
import Theorems.Thm_ChebotarevGeodesic_optimalExponent_le_of_hasErrorExponent
/-
# The optimal exponent in the prime geodesic / Chebotarev geodesic theorem

Second research cycle on top of `Shared.ChebotarevGeodesic` and
`Shared.ChebotarevGeodesicSharpness`.

Papers on the prime geodesic theorem are a history of successive numerical exponents
(`3/4`, `35/48`, `7/10`, `71/102`, `25/36`, …).  This file makes the notion of "the exponent
of a counting function" a *bona fide* real number and proves that it behaves as one expects:

* `exponentSet π M` — the set of admissible exponents — is an **upper set** and is **closed
  from below**: `hasErrorExponent_of_forall_gt` shows that if every `θ' > θ` works, then `θ`
  itself works.  This is the (slightly surprising) reason the `ε` in "`25/36 + ε`" can never
  be removed by a limiting argument alone, yet the *exponent* `25/36` is attained.
* Consequently `exponentSet π M = Ici (optimalExponent π M)` whenever it is non-empty and
  bounded below (`exponentSet_eq_Ici`), so there is a genuine **optimal exponent**, and it is
  attained (`hasErrorExponent_optimalExponent`).
* The record chain becomes a chain of inequalities for one real number:
  `optimalExponent ≤ 25/36` (`optimalExponent_le_of_hasErrorExponent`).
* A logarithmic form of the estimate (`log_abs_error_le`), which is the shape in which the
  exponent is usually extracted numerically, and a lower bound for the optimal exponent
  coming from genuine oscillation of the error term (`le_optimalExponent_of_growth`).
-/


open Filter Set
open scoped Topology

open ChebotarevGeodesic

variable {π M : ℝ → ℝ} {θ : ℝ}

/-! ## Closure of the exponent set from below -/





/-! ## The optimal exponent -/


variable (π M)



variable {π M}



/-! ## Logarithmic form -/


/-! ## Lower bounds for the optimal exponent -/

/-- Genuine oscillation of size `x^β` forces the optimal exponent to be at least `β`:
no analytic improvement below `β` is possible.  Combined with
`optimalExponent_le_of_hasErrorExponent` this brackets the true exponent. -/
theorem le_optimalExponent_of_growth {β c : ℝ} (hc : 0 < c)
    (hne : (exponentSet π M).Nonempty)
    (hgrow : ∀ x ≥ (1 : ℝ), c * x ^ β ≤ |π x - M x|) :
    β ≤ optimalExponent π M := by
  by_contra hlt
  push_neg at hlt
  exact not_hasErrorExponent_of_growth hc hlt hgrow
    (hasErrorExponent_optimalExponent π M hne)

/-- **Bracketing the exponent.**  If the error term is genuinely of size `x^β` and also
`O(x^{β+ε})` for all `ε > 0`, then the optimal exponent equals `β`. -/
theorem optimalExponent_eq_of_growth {β c : ℝ} (hc : 0 < c)
    (hbd : BddBelow (exponentSet π M))
    (hgrow : ∀ x ≥ (1 : ℝ), c * x ^ β ≤ |π x - M x|)
    (hupper : HasErrorExponent π M β) :
    optimalExponent π M = β := by
  have hne : (exponentSet π M).Nonempty := ⟨β, hupper⟩
  exact le_antisymm (optimalExponent_le_of_hasErrorExponent hbd hupper)
    (le_optimalExponent_of_growth hc hne hgrow)

/-! ## A computed optimal exponent -/




open ChebotarevGeodesic in
theorem solution(β : ℝ) :
    optimalExponent (fun x => x ^ β) (fun _ => 0) = β := by
  have hgrow : ∀ x ≥ (1 : ℝ), 1 * x ^ β ≤ |x ^ β - 0| := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have : (0 : ℝ) ≤ x ^ β := (Real.rpow_pos_of_pos hx0 β).le
    simp [abs_of_nonneg this]
  have hupper : HasErrorExponent (fun x => x ^ β) (fun _ => 0) β := by
    intro ε hε
    refine ⟨1, one_pos, 1, le_rfl, fun x hx => ?_⟩
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hle : x ^ β ≤ x ^ (β + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hpos : (0 : ℝ) ≤ x ^ β := (Real.rpow_pos_of_pos hx0 β).le
    simpa [abs_of_nonneg hpos] using hle
  have hbd : BddBelow (exponentSet (fun x => x ^ β) (fun _ => 0)) := by
    refine ⟨β, fun θ hθ => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact not_hasErrorExponent_of_growth one_pos hlt hgrow hθ
  exact optimalExponent_eq_of_growth one_pos hbd hgrow hupper
