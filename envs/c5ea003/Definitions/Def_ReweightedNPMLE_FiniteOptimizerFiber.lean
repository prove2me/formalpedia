-- Prove2me | Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
-- name    : ReweightedNPMLE_FiniteOptimizerFiber
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:14:46.768936+00:00
-- url     : https://prove2.me/theorems/1d9863b8-169f-4a70-aff4-f6987768869b
-- title:
--   Finite mixing simplices, fitted-value fibers, and coefficient supports
-- statement:
--   For a dictionary \(A_1,\ldots,A_m\) in a real vector space \(E\), define
--   \[
--   \Delta_m=\{p\in\mathbb R^m:p_j\ge0,\ \sum_jp_j=1\},
--   \quad V_A(p)=\sum_jp_jA_j,
--   \quad \mathcal F_A(v)=\{p\in\Delta_m:V_A(p)=v\}.
--   \]
--   Thus \(\mathcal F_A(v)\) contains all finite probability vectors producing the same fitted value \(v\). The augmented dictionary is \(\widetilde A_j=(1,A_j)\in\mathbb R\times E\), so its first coordinate records total mass. The coefficient support is the finite set \(\{j:p_j\ne0\}\); for a probability vector, these are exactly its positive coefficients. Repeated dictionary values remain separate indices until combined by the fitted-value map.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteOptimizerFiber.lean#L22-L81

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

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

namespace ReweightedNPMLE

/-- The probability simplex on a finite dictionary. -/
def finiteSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}







/-- Fitted value of a finite mixture. -/
def finiteMixtureValue {m : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (A : Fin m → E) (p : Fin m → ℝ) : E :=
  ∑ i, p i • A i



/-- Adding the total-mass coordinate turns affine independence of a finite
dictionary into ordinary linear independence. -/
def augmentedDictionary {m : ℕ} {E : Type*} (A : Fin m → E) : Fin m → ℝ × E :=
  fun i ↦ (1, A i)

/-- Fiber of all finite mixing weights representing the fitted value `v`. -/
def finiteMixtureFiber {m : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (A : Fin m → E) (v : E) :
    Set (Fin m → ℝ) :=
  {p | p ∈ finiteSimplex m ∧ finiteMixtureValue A p = v}





/-- Indices carrying nonzero mass. -/
noncomputable def coefficientSupport {m : ℕ} (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ p i ≠ 0





























end ReweightedNPMLE


