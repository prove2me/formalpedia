-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_rational_noisy_decoder_singleton
-- name    : Couret.STROBO2TORS.recoh_rational_noisy_decoder_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:49.848386+00:00
-- url     : https://prove2.me/theorems/4525d12e-3a41-40ba-89c4-e65a0768d663
-- title:
--   Completeness and strict separation give exact noisy recovery
-- statement:
--   Let $X,I$ be types, $r:X\to\mathbb C^I$, $C\subseteq X$ finite, and $o\in\mathbb C^I$. Assume $X$ has decidable equality and $I$ is finite. Let rational-complex predictions $p(A)_i$ and observations $o_i$ be interpreted in $\mathbb C$, and let $\rho\in\mathbb Q$. Define $D$ by retaining $A\in C$ when $\rho\ge0$ and every rational squared distance $|o_i-p(A)_i|^2\le\rho^2$. A bank is $\delta$-separated on a candidate set when every two distinct candidates have at least one reading whose distance is at least $\delta$. Suppose $\rho\ge0$, $A\in C$, $r$ is $\delta$-separated on $C$, all prediction errors are at most $\eta$, the observation error relative to $A$ is at most $e$ coordinatewise, $e+\eta\le\rho$, and $2(\rho+\eta)<\delta$. Then
--
--   $$D=\{A\}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisyUniqueness.lean#L162-L186, lines 162–186; source file SHA-256 6052faa2e2efbc2d3e68381058002e13b4872e2433fd587269e83b1de0f67f8c; theorem Couret.STROBO2TORS.recoh_rational_noisy_decoder_singleton

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_prediction_sound
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_ball_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_noisy_decoder_card_le_one
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

theorem recoh_rational_noisy_decoder_singleton {X I : Type*}
    [DecidableEq X] [Fintype I]
    (reading : X → I → ℂ) (candidates : Finset X)
    (predicted : X → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) (ε η δ : ℝ)
    (hradius : 0 ≤ radius) (S : X) (hS : S ∈ candidates)
    (hsep : RecohReadingSeparated reading candidates δ)
    (hpred : ∀ T ∈ candidates, ∀ i,
      ‖recohRationalComplexValue (predicted T i) - reading T i‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) - reading S i‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : 2 * ((radius : ℝ) + η) < δ) :
    recohRationalNoisyDecoder candidates predicted observed radius = {S} := by sorry






end Couret.STROBO2TORS
