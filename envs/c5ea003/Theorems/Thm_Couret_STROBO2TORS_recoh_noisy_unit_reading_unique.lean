-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_unit_reading_unique
-- name    : Couret.STROBO2TORS.recoh_noisy_unit_reading_unique
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:24.890542+00:00
-- url     : https://prove2.me/theorems/c6a9495b-4ede-4143-b020-b8c998c24cfd
-- title:
--   Strict coordinatewise unit errors identify a two-separated candidate
-- statement:
--   Let $X,I$ be types, $r:X\to\mathbb C^I$, $C\subseteq X$ finite, and $o\in\mathbb C^I$. A bank is $\delta$-separated on a candidate set when every two distinct candidates have at least one reading whose distance is at least $\delta$. If $r$ is two-separated on $C$, $A,B\in C$, and $|o_i-r(A)_i|<1$, $|o_i-r(B)_i|<1$ for every $i$, then
--
--   $$A=B.$$
--
--   No common strict error maximum or finite index type is required.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisyUniqueness.lean#L52-L71, lines 52–71; source file SHA-256 6052faa2e2efbc2d3e68381058002e13b4872e2433fd587269e83b1de0f67f8c; theorem Couret.STROBO2TORS.recoh_noisy_unit_reading_unique

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

theorem recoh_noisy_unit_reading_unique {X I : Type*}
    (reading : X → I → ℂ) (candidates : Finset X)
    (hsep : RecohReadingSeparated reading candidates 2)
    (observed : I → ℂ) (S T : X) (hS : S ∈ candidates) (hT : T ∈ candidates)
    (hSerr : ∀ i, ‖observed i - reading S i‖ < 1)
    (hTerr : ∀ i, ‖observed i - reading T i‖ < 1) : S = T := by sorry




















end Couret.STROBO2TORS
