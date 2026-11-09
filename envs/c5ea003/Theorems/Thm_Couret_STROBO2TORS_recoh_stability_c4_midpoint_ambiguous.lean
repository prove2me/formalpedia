-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stability_c4_midpoint_ambiguous
-- name    : Couret.STROBO2TORS.recoh_stability_c4_midpoint_ambiguous
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:06.605192+00:00
-- url     : https://prove2.me/theorems/5d9e8a04-4b7f-479c-ba37-0e0fc90e75d5
-- title:
--   Every C4 character bank admits observations ambiguous at unit error
-- statement:
--   For any index type $I$ and complex additive-character bank $\chi_i$ on $\mathbb Z/4\mathbb Z$, there exists $o\in\mathbb C^I$ such that for the two C4 collision supports $A=\{0,1,2\}$ and $B=\{0,2,3\}$,
--
--   $$|o_i-P_{\chi_i}(A)|\le1,\qquad|o_i-P_{\chi_i}(B)|\le1\quad(i\in I).$$
--
--   This remains true for arbitrarily large or infinite banks.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisyUniqueness.lean#L201-L211, lines 201–211; source file SHA-256 6052faa2e2efbc2d3e68381058002e13b4872e2433fd587269e83b1de0f67f8c; theorem Couret.STROBO2TORS.recoh_stability_c4_midpoint_ambiguous

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_stability_c4_probe_upper
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

theorem recoh_stability_c4_midpoint_ambiguous
    {I : Type*} (bank : I → AddChar (ZMod 4) ℂ) :
    ∃ observed : I → ℂ, ∀ i,
      ‖observed i - recohSupportProbe (bank i) recohStabilityC4Left‖ ≤ 1 ∧
      ‖observed i - recohSupportProbe (bank i) recohStabilityC4Right‖ ≤ 1 := by sorry


end Couret.STROBO2TORS
