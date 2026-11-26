-- Prove2me | Theorems.Thm_ReweightedNPMLE_finiteMixtureFiber_extreme_of_linearIndepOn
-- name    : ReweightedNPMLE.finiteMixtureFiber_extreme_of_linearIndepOn
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:38:07.63248+00:00
-- url     : https://prove2.me/theorems/955ffc8c-9a3f-43f6-9d1e-98d0ec408ad5
-- title:
--   An independent active dictionary makes a finite mixture extreme
-- statement:
--   Let $E$ be a real vector space, let $A_1,\ldots,A_m\in E$, and define the fitted-value fiber
--   $$F_v=\{p\in[0,\infty)^m:\sum_i p_i=1,\ \sum_i p_iA_i=v\}.$$
--   Suppose $p\in F_v$ and the vectors $(A_i)_{i:p_i>0}$ are linearly independent. Then $p$ is an extreme point of $F_v$: any representation $p=(1-t)q+tr$ with $q,r\in F_v$ and $0<t<1$ forces $q=r=p$. No topology on $E$ or likelihood-optimality assumption is required.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteOptimizerFiber.lean#L91-L143

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber

/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.finiteMixtureFiber_extreme_of_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ finiteMixtureFiber A v)
    (hlin : LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m))) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ := by sorry
