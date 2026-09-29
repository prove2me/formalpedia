-- Prove2me | solution 1 for ChebotarevGeodesic.hasErrorExponent_optimalExponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:52:16.737406+00:00
-- url     : https://prove2.me/submissions/2189433c-4c90-4747-a333-0fc931d67de5

-- Sol generated from Shared/ChebotarevGeodesicOptimal.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Theorems.Thm_ChebotarevGeodesic_HasErrorExponent_mono
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

/-- **The exponent set is closed from below.**  If every exponent strictly larger than `θ`
is admissible, then `θ` itself is admissible.  (The point is that the definition already
carries an `ε`; a diagonal argument in `ε` does the rest.) -/
theorem hasErrorExponent_of_forall_gt (h : ∀ θ' > θ, HasErrorExponent π M θ') :
    HasErrorExponent π M θ := by
  intro ε hε
  obtain ⟨C, hC, X, hX, hb⟩ := h (θ + ε / 2) (by linarith) (ε / 2) (by linarith)
  refine ⟨C, hC, X, hX, fun x hx => ?_⟩
  have := hb x hx
  have heq : θ + ε / 2 + ε / 2 = θ + ε := by ring
  rwa [heq] at this




/-! ## The optimal exponent -/


variable (π M)



variable {π M}



/-! ## Logarithmic form -/


/-! ## Lower bounds for the optimal exponent -/



/-! ## A computed optimal exponent -/




open ChebotarevGeodesic in
theorem solution(hne : (exponentSet π M).Nonempty) :
    HasErrorExponent π M (optimalExponent π M) := by
  refine hasErrorExponent_of_forall_gt fun θ' hθ' => ?_
  obtain ⟨θ'', hmem, hlt⟩ := Real.lt_sInf_add_pos hne
    (show 0 < θ' - optimalExponent π M by
      simpa [optimalExponent] using sub_pos.mpr hθ')
  have : θ'' < θ' := by
    have : θ'' < sInf (exponentSet π M) + (θ' - optimalExponent π M) := hlt
    simpa [optimalExponent] using this
  exact (hmem : HasErrorExponent π M θ'').mono this.le
