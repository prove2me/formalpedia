-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_prediction_sound
-- name    : Couret.STROBO2TORS.recoh_noisy_prediction_sound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:28.248193+00:00
-- url     : https://prove2.me/theorems/a00add81-e062-44b2-8a0d-9cc8e4ffe21b
-- title:
--   Prediction and fitting errors add
-- statement:
--   For complex $t,p,o$ and real $\eta,\tau$, if $|p-t|\le\eta$ and $|o-p|\le\tau$, then
--
--   $$|o-t|\le\tau+\eta.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisyUniqueness.lean#L40-L50, lines 40–50; source file SHA-256 6052faa2e2efbc2d3e68381058002e13b4872e2433fd587269e83b1de0f67f8c; theorem Couret.STROBO2TORS.recoh_noisy_prediction_sound

import Aesop
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
Noise tolerance with explicit prediction error.  The executable decoder
below compares rational squared distances.  Its correctness theorem relates
those comparisons to the complex readings, accounting separately for the
measurement error, the prediction error, and the acceptance radius.

The candidate set is supplied explicitly.  Completeness requires the true
support to occur in that set; this module makes no ambient enumeration claim.
-/

namespace Couret.STROBO2TORS

theorem recoh_noisy_prediction_sound (truth prediction observed : ℂ)
    (η τ : ℝ) (hpred : ‖prediction - truth‖ ≤ η)
    (hfit : ‖observed - prediction‖ ≤ τ) :
    ‖observed - truth‖ ≤ τ + η := by sorry






















end Couret.STROBO2TORS
