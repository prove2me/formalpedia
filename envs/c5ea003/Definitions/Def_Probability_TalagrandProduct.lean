-- Prove2me | Definitions.Def_Probability_TalagrandProduct
-- name    : Probability_TalagrandProduct
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:25.355315+00:00
-- url     : https://prove2.me/theorems/7c4860d8-49f1-443b-b105-7f0f06f6a1ed
-- title:
--   Aether Catalog definitions — Probability_TalagrandProduct
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandProduct`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandProduct.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandRep

/-!
# Talagrand's convex-distance inequality on finite product spaces

Let `α` be a finite alphabet and let `p i` be a probability weight on `α` for each
coordinate `i : Fin n` (the coordinates are independent but need *not* be
identically distributed).  Equip `Fin n → α` with the product measure
`Talagrand.mass p`.  The main theorem of this file is the exponential moment bound

  `Eexp p A * mass p A ≤ 1`,  where  `Eexp p A = ∑ x, wt p x * exp (dTsq A x / 4)`,

for every `A : Finset (Fin n → α)`.  This is Talagrand's convex-distance
inequality (with the explicit constant `1/4` in the exponent), proved by
induction on the number of coordinates.  The i.i.d. case is recorded separately as
`Talagrand.Eexp_mul_mass_le_one_iid`.

The three ingredients are

* `Talagrand.exists_isRepW_mix` — the geometric step: a convex combination of a
  representation of the section `sec A a` and a representation of the
  projection `proj A` represents `A` at `Fin.cons a y`, at the price of one unit
  in the new coordinate;
* `Talagrand.weighted_holder` — Hölder's inequality, used to interpolate the two
  inductive hypotheses;
* `Talagrand.exists_lambda_bound` — the scalar interpolation lemma
  `inf_lam exp ((1-lam)^2/4) r ^ (-lam) ≤ 2 - r`.

-/

namespace Talagrand

open Finset Real

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The product measure -/

/-- The product weight of a point of `Fin n → α`, for a *coordinatewise* family of
weights `p i` (the coordinates need not be identically distributed). -/
def wt {n : ℕ} (p : Fin n → α → ℝ) (x : Fin n → α) : ℝ := ∏ i, p i (x i)

/-- The product measure of a finite set of points. -/
def mass {n : ℕ} (p : Fin n → α → ℝ) (S : Finset (Fin n → α)) : ℝ := ∑ x ∈ S, wt p x

/-- The exponential moment of Talagrand's squared convex distance to `A`. -/
noncomputable def Eexp {n : ℕ} (p : Fin n → α → ℝ) (A : Finset (Fin n → α)) : ℝ :=
  ∑ x : Fin n → α, wt p x * Real.exp (dTsq A x / 4)









/-! ### Sections and projections -/

/-- The section of `A` above the letter `a` in the first coordinate. -/
def sec {n : ℕ} (A : Finset (Fin (n + 1) → α)) (a : α) : Finset (Fin n → α) :=
  Finset.univ.filter (fun y => Fin.cons a y ∈ A)

/-- The projection of `A` forgetting the first coordinate. -/
def proj {n : ℕ} (A : Finset (Fin (n + 1) → α)) : Finset (Fin n → α) :=
  Finset.univ.filter (fun y => ∃ a, Fin.cons a y ∈ A)





/-! ### Transfer of sums over `A` to sums over sections and projections -/



/-! ### The geometric step -/



/-! ### The exponential moment bound -/




/-! ### The i.i.d. special case -/

/-- The i.i.d. family of coordinate weights attached to a single weight `p`. -/
def iid (p : α → ℝ) (n : ℕ) : Fin n → α → ℝ := fun _ => p



end Talagrand


