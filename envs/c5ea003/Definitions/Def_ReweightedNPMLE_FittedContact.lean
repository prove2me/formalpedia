-- Prove2me | Definitions.Def_ReweightedNPMLE_FittedContact
-- name    : ReweightedNPMLE_FittedContact
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:17:08.296262+00:00
-- url     : https://prove2.me/theorems/9f9be214-43c1-5507-8878-fea6d6cf5210
-- title:
--   The likelihood contact numerator and normalized functional
-- statement:
--   For weight and fitted-value vectors \(w,v\in\mathbb R^n\), define
--   \[
--   N_{w,v}(a)=\sum_iw_i\frac{a_i}{v_i},\qquad
--   L_{w,v}(a)=\sum_i\frac{w_i}{v_iT(w)}a_i,
--   \quad T(w)=\sum_iw_i.
--   \]
--   The normalized expression is a real linear functional of \(a\). When \(v_i>0\) and \(T(w)\ne0\), it equals \(N_{w,v}(a)/T(w)\) and satisfies \(L_{w,v}(v)=1\). The directional derivative of \(\ell_w\) at \(v\) toward \(a\) is \(N_{w,v}(a)-T(w)\), which links the functional to the supporting contact hyperplane at an optimizer. Zero denominators contribute zero under the formal real-division convention.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedContact.lean#L21-L80

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE

/-- The unnormalized directional derivative of weighted log likelihood at
`v`, applied to a candidate fitted vector `a`. -/
noncomputable def likelihoodContactNumerator {n : ℕ}
    (w v a : Fin n → ℝ) : ℝ :=
  ∑ i, w i * (a i / v i)


  
/-- The normalized likelihood contact functional `a ↦ Σᵢ wᵢaᵢ/(vᵢΣw)`.
It is defined as zero only in the degenerate case `Σw = 0`; the theorems below
use positive weights. -/
noncomputable def likelihoodContactFunctional {n : ℕ}
    (w v : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin n,
    (w i / (v i * total w)) • LinearMap.proj i













end ReweightedNPMLE


