-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_reading_unique
-- name    : Couret.STROBO2TORS.recoh_noisy_reading_unique
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:36.481636+00:00
-- url     : https://prove2.me/theorems/f7d40949-364f-470a-aaef-a6b4b264f792
-- title:
--   Two candidates within a strict separation budget coincide
-- statement:
--   Let $X,I$ be types, $r:X\to\mathbb C^I$, $C\subseteq X$ finite, and $o\in\mathbb C^I$. A bank is $\delta$-separated on a candidate set when every two distinct candidates have at least one reading whose distance is at least $\delta$. Suppose $r$ is $\delta$-separated on $C$, $A,B\in C$, and for real $e_A,e_B$, all coordinate errors from $o$ are bounded by $e_A,e_B$ respectively. Then
--
--   $$e_A+e_B<\delta\Longrightarrow A=B.$$
--
--   The index type need not be finite.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisyUniqueness.lean#L19-L38, lines 19–38; source file SHA-256 6052faa2e2efbc2d3e68381058002e13b4872e2433fd587269e83b1de0f67f8c; theorem Couret.STROBO2TORS.recoh_noisy_reading_unique

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

theorem recoh_noisy_reading_unique {X I : Type*}
    (reading : X → I → ℂ) (candidates : Finset X) (δ : ℝ)
    (hsep : RecohReadingSeparated reading candidates δ)
    (observed : I → ℂ) (S T : X) (hS : S ∈ candidates) (hT : T ∈ candidates)
    (εS εT : ℝ) (hbudget : εS + εT < δ)
    (hSerr : ∀ i, ‖observed i - reading S i‖ ≤ εS)
    (hTerr : ∀ i, ‖observed i - reading T i‖ ≤ εT) : S = T := by sorry
























end Couret.STROBO2TORS
