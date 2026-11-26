-- Prove2me | Theorems.Thm_ReweightedNPMLE_augmented_linearIndepOn_of_finiteMixtureFiber_extreme
-- name    : ReweightedNPMLE.augmented_linearIndepOn_of_finiteMixtureFiber_extreme
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:44.874701+00:00
-- url     : https://prove2.me/theorems/945b89fc-973b-419b-b57a-697971dfee16
-- title:
--   An extreme finite probability mixture has an affinely independent active dictionary
-- statement:
--   Let $E$ be a real vector space and let
--   $$F_v=\{p\ge0:\sum_i p_i=1,\ \sum_i p_iA_i=v\}$$
--   for a finite dictionary $A_1,\ldots,A_m\in E$. If $p$ is an extreme point of $F_v$, then the augmented vectors $(1,A_i)$ with $p_i>0$ are linearly independent. Thus affine independence of the active dictionary is necessary for extremality, complementing the sufficient criterion. The conclusion uses the mass constraint as well as the fitted-value constraint; ordinary linear independence is not asserted in this general setting.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteOptimizerFiber.lean#L225-L343

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

theorem ReweightedNPMLE.augmented_linearIndepOn_of_finiteMixtureFiber_extreme
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ)
    (hp : p ∈ (finiteMixtureFiber A v).extremePoints ℝ) :
    LinearIndepOn ℝ (augmentedDictionary A)
      (coefficientSupport p : Set (Fin m)) := by sorry
