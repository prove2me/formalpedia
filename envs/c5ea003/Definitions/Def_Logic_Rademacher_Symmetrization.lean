-- Prove2me | Definitions.Def_Logic_Rademacher_Symmetrization
-- name    : Logic_Rademacher_Symmetrization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:21.750626+00:00
-- url     : https://prove2.me/theorems/e628162f-f917-45e4-bfb8-0b1acfb200e9
-- title:
--   Aether Catalog definitions — Logic_Rademacher_Symmetrization
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Rademacher.Symmetrization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Rademacher/Symmetrization.lean by skeleton subtraction
import Mathlib
/-
# The generalization bound: symmetrization

For a finite hypothesis class `F` of real valued functions on a finite domain `X`,
an arbitrary probability vector `p` on `X`, and i.i.d. samples `S ∈ Xⁿ`, the expected
uniform deviation between the true mean and the empirical mean is at most twice the
expected empirical Rademacher complexity:

  `𝔼_S sup_{f ∈ F} (𝔼_p f − Ê_S f) ≤ 2 · 𝔼_S R̂_S(F)`.

This is the classical *symmetrization* inequality, the reason Rademacher complexity
controls generalization.  Everything is finite here: expectations are explicit weighted
sums over `Xⁿ`, so no measure theory is required and the argument is completely
elementary — but not trivial: the heart of the proof is that for each sign pattern `ε`
the map exchanging the `i`-th points of the sample and of the ghost sample whenever
`ε i = false` is a weight preserving involution of `Xⁿ × Xⁿ`.

This file is self-contained.
-/

namespace RademacherSymmetrization

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- The sign vector attached to a boolean vector: `true ↦ 1`, `false ↦ -1`. -/
def sgn (ε : Fin n → Bool) (i : Fin n) : ℝ := if ε i then 1 else -1



/-- The probability of the sample `S` under the product measure. -/
def wt (p : X → ℝ) (S : Fin n → X) : ℝ := ∏ i, p (S i)

/-- The empirical mean of `f` on the sample `S`. -/
noncomputable def emp (S : Fin n → X) (f : X → ℝ) : ℝ := (1 / (n:ℝ)) * ∑ i, f (S i)

/-- The true mean of `f` under `p`. -/
def mean (p : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, p x * f x

/-- The signed empirical average of `f` on the sample `S` for the sign pattern `ε`. -/
noncomputable def corr (ε : Fin n → Bool) (S : Fin n → X) (f : X → ℝ) : ℝ :=
  (1 / (n:ℝ)) * ∑ i, sgn ε i * f (S i)

/-- The maximal signed empirical average over the class. -/
noncomputable def maxCorr (F : Finset (X → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool)
    (S : Fin n → X) : ℝ := F.sup' hne (corr ε S)

/-- The empirical Rademacher complexity of `F` on the sample `S`. -/
noncomputable def radS (F : Finset (X → ℝ)) (hne : F.Nonempty) (S : Fin n → X) : ℝ :=
  (∑ ε : Fin n → Bool, maxCorr F hne ε S) / 2 ^ n

/-- The uniform deviation between true and empirical means on the sample `S`. -/
noncomputable def gap (F : Finset (X → ℝ)) (hne : F.Nonempty) (p : X → ℝ)
    (S : Fin n → X) : ℝ := F.sup' hne (fun f => mean p f - emp S f)

/-! ### The product measure -/





/-! ### Step 1: introducing the ghost sample -/

/-- The maximal difference of empirical means between the ghost sample `S'` and the
sample `S`. -/
noncomputable def ghostGap (F : Finset (X → ℝ)) (hne : F.Nonempty)
    (S S' : Fin n → X) : ℝ := F.sup' hne (fun f => emp S' f - emp S f)


/-! ### Step 2: the swapping involution -/

/-- Exchange the `i`-th points of the sample and the ghost sample whenever `ε i = false`. -/
def swapPair (ε : Fin n → Bool) (q : (Fin n → X) × (Fin n → X)) :
    (Fin n → X) × (Fin n → X) :=
  (fun i => if ε i then q.1 i else q.2 i, fun i => if ε i then q.2 i else q.1 i)




/-! ### Step 3: the symmetrized quantity is bounded by two Rademacher terms -/


/-! ### The generalization bound -/


/-! ### A Massart bound for the empirical Rademacher complexity of a finite class

To turn the symmetrization inequality into a concrete generalization bound we bound the
empirical Rademacher complexity of a finite class of uniformly bounded functions by the
Chernoff/moment generating function argument, exactly as in Massart's finite class
lemma.
-/








end RademacherSymmetrization


