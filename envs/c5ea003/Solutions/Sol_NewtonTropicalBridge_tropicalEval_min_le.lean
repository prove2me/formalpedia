-- Prove2me | solution 1 for NewtonTropicalBridge.tropicalEval_min_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:14:23.037674+00:00
-- url     : https://prove2.me/submissions/726d4bcb-b3ea-459c-8592-a492ceb88862

-- Sol generated from Bridges/TropicalAlgebra/NewtonTropicalBridge.lean
import Mathlib
import Definitions.Def_Bridges_TropicalAlgebra_NewtonTropicalBridge
/-
  # Newton–Tropical Bridge:
  # Polynomial Valuation Profiles, Tropical Evaluation,
  # and Cryptographic Root Certificates

  ## Domain Bridge: Number Theory ↔ Tropical Geometry ↔ Cryptography

  The Newton polygon of a polynomial f(x) = ∑ aᵢxⁱ with respect to a
  p-adic valuation v is encoded by the **valuation profile** i ↦ v(aᵢ).
  The **tropical evaluation** of this profile at a point t ∈ ℕ∞ is
    T_f(t) = inf_i (v(aᵢ) + i · t)
  which is the lower envelope of the Newton polygon.

  ## Main Results

  1. `NewtonProfile` — novel structure: the valuation profile of a polynomial
  2. `tropicalEval` — tropical polynomial evaluation (lower envelope)
  3. `tropicalEval_at_zero` — evaluation at zero gives min coefficient valuation
  4. `tropicalEval_min_le` — min of profiles dominates eval of min profile
  5. `tropical_eval_at_root_le` — bridge theorem: v(f(a)) ≥ T_f(v(a))
  6. `NewtonSlopeCertificate` — cryptographic certificate structure
  7. `tropicalEval_stable` — stability under profile perturbation
  8. `dominant_lt_nondominant` — dominant term analysis
-/


open Finset BigOperators WithTop

noncomputable section

open NewtonTropicalBridge

/-! ## §1. Newton Valuation Profile -/



/-! ## §2. Tropical Polynomial Evaluation -/


/-! ## §3. Properties of Tropical Evaluation -/



/-! ## §4. Dominant Term Analysis -/




/-! ## §5. Profile Operations -/



/-! ## §6. Root–Valuation Bridge Theorem -/

/-
Helper: v(aⁿ) = n · v(a) for multiplicative valuations.
-/

/-
**Root–Valuation Bridge**: v(∑ cᵢ · aⁱ) ≥ T_profile(v(a)).
The p-adic valuation of a polynomial value is bounded below by
the tropical evaluation of the Newton profile.
-/

/-! ## §7. Stability of Tropical Evaluation -/


/-
**Stability**: ε-close profiles have tropical evaluations within ε.
-/

/-! ## §8. Newton Slope Certificate -/




/-! ## §9. Valued Polynomial Structure -/





/-! ## §10. Tropical Discriminant -/



/-! ## §11. Infimal Convolution (Tropical Product) -/


/-
The infimal convolution at k = 0 is bounded by pA(0) + pB(0).
-/

/-! ## §12. Falsifiable Conjecture -/

 -- Full statement requires p-adic root theory

/-! ## §13. Computational Helpers -/



open NewtonTropicalBridge in
theorem solution{n : ℕ} (pA pB : NewtonProfile n) (t : ℕ∞) :
    tropicalEval (profileMin pA pB) t ≤
    min (tropicalEval pA t) (tropicalEval pB t) := by
  apply le_min
  · apply Finset.le_inf'
    intro i _
    calc tropicalEval (profileMin pA pB) t
        ≤ min (pA.profile i) (pB.profile i) + (↑↑i) * t :=
          Finset.inf'_le _ (Finset.mem_univ i)
      _ ≤ pA.profile i + (↑↑i) * t := add_le_add (min_le_left _ _) le_rfl
  · apply Finset.le_inf'
    intro i _
    calc tropicalEval (profileMin pA pB) t
        ≤ min (pA.profile i) (pB.profile i) + (↑↑i) * t :=
          Finset.inf'_le _ (Finset.mem_univ i)
      _ ≤ pB.profile i + (↑↑i) * t := add_le_add (min_le_right _ _) le_rfl
