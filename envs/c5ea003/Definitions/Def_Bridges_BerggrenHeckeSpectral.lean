-- Prove2me | Definitions.Def_Bridges_BerggrenHeckeSpectral
-- name    : Bridges_BerggrenHeckeSpectral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:36.987453+00:00
-- url     : https://prove2.me/theorems/14f901e7-1feb-4e76-b7f3-00f7cf4f4c2c
-- title:
--   Aether Catalog definitions — Bridges_BerggrenHeckeSpectral
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenHeckeSpectral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenHeckeSpectral.lean by skeleton subtraction
import Mathlib

/-!
# Berggren–Hecke Spectral Reconstruction on the Pythagorean Tree

We construct a finite spectral reconstruction theory on the Berggren tree of primitive
Pythagorean triples, establishing a new bridge between Diophantine geometry, commutative
operator algebras on arithmetic trees, and certified signal recovery.

## Main results

1. **Pythagorean preservation** (`berggrenChild_isPythagorean`, `berggrenEval_isPythagorean`):
   Every vertex of the Berggren tree corresponds to a Pythagorean triple.

2. **Residue class stability** (`berggrenChild_residue_commutes`):
   The residue class `(a,b,c) mod K` of a Berggren triple factors through the
   parent's residue class and the branch index.

3. **Commutative operator algebra** (`translateLMap_commute`, `heckeOp_translate_commute`):
   Translation operators on the finite word state space `(ℤ/3ℤ)^n` form a
   commutative algebra, and the Hecke averaging operator commutes with all translations.

4. **Finite order** (`translateLMap_cubed`): Every translation operator has order
   dividing 3, reflecting the `ℤ/3ℤ` structure of the Berggren branching.

5. **Character separation** (`moment_pointChar_eq`, `signal_eq_of_all_moments_eq`):
   Point-evaluation characters separate signals, and the moment map is injective.

6. **Certified reconstruction** (`berggrenHecke_certified_reconstruction`):
   Signals on the Berggren tree are uniquely determined by finitely many character
   moments, via a finite spectral reconstruction principle.

7. **Branch-periodic signal theory** (`branchPeriodic_factors_through_prefix`,
   `branchPeriodic_moment_injective`):
   Branch-periodic signals factor through a finite quotient, and the moment map
   restricted to periodic signals remains injective.

## Mathematical significance

This establishes the Berggren tree as an **arithmetic computation medium**: a
noncommutative tree whose commutative spectral observables admit certified
hidden-structure recovery. The key bridge is:

> Although the raw Berggren child maps do not commute, suitable translation/averaging
> operators on the word state space form a commutative algebra whose characters
> encode enough information to reconstruct hidden branch periodicity.
-/

open Finset Function

namespace BerggrenHecke

/-! ## Section 1: Berggren Tree Core

The Berggren tree generates all primitive Pythagorean triples from `(3,4,5)`
via three integer matrices. We define child maps and prove Pythagorean preservation.
-/

/-- A triple `(a,b,c)` is Pythagorean if `a² + b² = c²`. -/
def IsPythagorean (t : ℤ × ℤ × ℤ) : Prop :=
  t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2

/-- Apply the `i`-th Berggren child matrix to an integer triple.
- `B₁ = [[1,-2,2],[2,-1,2],[2,-2,3]]`
- `B₂ = [[1,2,2],[2,1,2],[2,2,3]]`
- `B₃ = [[-1,2,2],[-2,1,2],[-2,2,3]]` -/
def berggrenChild (i : Fin 3) (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  match i with
  | ⟨0, _⟩ => (t.1 - 2*t.2.1 + 2*t.2.2,
               2*t.1 - t.2.1 + 2*t.2.2,
               2*t.1 - 2*t.2.1 + 3*t.2.2)
  | ⟨1, _⟩ => (t.1 + 2*t.2.1 + 2*t.2.2,
               2*t.1 + t.2.1 + 2*t.2.2,
               2*t.1 + 2*t.2.1 + 3*t.2.2)
  | ⟨2, _⟩ => (-t.1 + 2*t.2.1 + 2*t.2.2,
               -2*t.1 + t.2.1 + 2*t.2.2,
               -2*t.1 + 2*t.2.1 + 3*t.2.2)

/-- Evaluate a Berggren word (branch path) to get the corresponding triple.
The word is read right-to-left: the last element is applied first. -/
def berggrenEval : List (Fin 3) → ℤ × ℤ × ℤ
  | [] => (3, 4, 5)
  | i :: w => berggrenChild i (berggrenEval w)





/-! ## Section 2: Residue Class Stability

Since the Berggren matrices have integer entries, the residue class `(a,b,c) mod K`
of a child depends only on the parent's residue class and the branch index.
-/

/-- The residue class of a triple modulo `K`. -/
def tripleResidue (K : ℕ) (t : ℤ × ℤ × ℤ) : ZMod K × ZMod K × ZMod K :=
  (↑t.1, ↑t.2.1, ↑t.2.2)

/-- The Berggren child map on residue classes modulo `K`. -/
def berggrenChildResidue (K : ℕ) (i : Fin 3) (r : ZMod K × ZMod K × ZMod K) :
    ZMod K × ZMod K × ZMod K :=
  match i with
  | ⟨0, _⟩ => (r.1 - 2*r.2.1 + 2*r.2.2,
               2*r.1 - r.2.1 + 2*r.2.2,
               2*r.1 - 2*r.2.1 + 3*r.2.2)
  | ⟨1, _⟩ => (r.1 + 2*r.2.1 + 2*r.2.2,
               2*r.1 + r.2.1 + 2*r.2.2,
               2*r.1 + 2*r.2.1 + 3*r.2.2)
  | ⟨2, _⟩ => (-r.1 + 2*r.2.1 + 2*r.2.2,
               -2*r.1 + r.2.1 + 2*r.2.2,
               -2*r.1 + 2*r.2.1 + 3*r.2.2)


/-- The residue class along a Berggren path via iterated residue child map. -/
def berggrenEvalResidue (K : ℕ) : List (Fin 3) → ZMod K × ZMod K × ZMod K
  | [] => tripleResidue K (3, 4, 5)
  | i :: w => berggrenChildResidue K i (berggrenEvalResidue K w)



/-! ## Section 3: Finite Word State Space

Depth-`n` Berggren tree vertices are modeled as words `Fin n → Fin 3`.
This finite type has `3^n` elements and carries abelian group structure
from pointwise `ℤ/3ℤ` addition.
-/

/-- Words of length `n` over `{0,1,2}` — depth-`n` Berggren tree vertices. -/
abbrev WordState (n : ℕ) := Fin n → Fin 3


instance wordState_inhabited (n : ℕ) : Inhabited (WordState n) := ⟨0⟩

/-! ## Section 4: Translation Operators and the Hecke Algebra

Translation by `v ∈ (ℤ/3ℤ)^n` sends signal `f` to `f(· + v)`. These form
a commutative algebra since the underlying group is abelian.
-/

/-- Translate a signal by word vector `v`: `(T_v f)(w) = f(w + v)`. -/
def translateSignal {n : ℕ} (v : WordState n) {R : Type*} (f : WordState n → R) :
    WordState n → R :=
  fun w => f (w + v)



/-- Translation as an `R`-linear map on the signal module. -/
def translateLMap {n : ℕ} (v : WordState n) (R : Type*) [CommSemiring R] :
    (WordState n → R) →ₗ[R] (WordState n → R) where
  toFun f w := f (w + v)
  map_add' f g := by ext; simp [Pi.add_apply]
  map_smul' r f := by ext; simp [Pi.smul_apply]






/-- The Hecke averaging operator: `(H f)(w) = ∑_v f(w + v)`.
This sums a signal over all translates, producing a "total mass" observable. -/
noncomputable def heckeOp (n : ℕ) (R : Type*) [CommSemiring R] :
    (WordState n → R) →ₗ[R] (WordState n → R) where
  toFun f w := ∑ v : WordState n, f (w + v)
  map_add' f g := by ext w; simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r f := by ext w; simp [Pi.smul_apply, Finset.mul_sum]



/-! ## Section 5: Characters and the Moment Map

Point-evaluation characters form a separating family for signals on the finite
state space. The moment map (pairing with test functions) is therefore injective.
-/

/-- Point indicator (character): `δ_v(w) = if w = v then 1 else 0`. -/
noncomputable def pointChar {n : ℕ} (v : WordState n) : WordState n → ℚ :=
  fun w => if w = v then 1 else 0

/-- The moment of a signal `f` against test function `χ`:
`⟨f, χ⟩ = ∑_w f(w) · χ(w)`. -/
noncomputable def moment {n : ℕ} (f χ : WordState n → ℚ) : ℚ :=
  ∑ w : WordState n, f w * χ w


/-- The moment map sending `f` to its vector of point-character moments. -/
noncomputable def momentMap (n : ℕ) : (WordState n → ℚ) →ₗ[ℚ] (WordState n → ℚ) where
  toFun f v := moment f (pointChar v)
  map_add' f g := by
    ext v; simp [moment, pointChar, Pi.add_apply]
  map_smul' r f := by
    ext v; simp [moment, pointChar, Pi.smul_apply, mul_comm r]




/-! ## Section 6: Certified Spectral Reconstruction

We combine separation with a generic reconstruction principle.
-/

/-- The separating family of point characters. -/
noncomputable def charFamily (n : ℕ) : Finset (WordState n → ℚ) :=
  Finset.univ.image pointChar





/-! ## Section 7: Branch-Periodic Signals

A signal is branch-periodic with period `p` if it depends only on the prefix
of length `p`. Such signals factor through a finite quotient.
-/

/-- A signal is `p`-periodic if it depends only on the first `p` coordinates. -/
def BranchPeriodic {n : ℕ} (p : ℕ) (_hp : p ≤ n) (f : WordState n → ℚ) : Prop :=
  ∀ w₁ w₂ : WordState n, (∀ i : Fin n, (i : ℕ) < p → w₁ i = w₂ i) → f w₁ = f w₂

/-- Prefix truncation: restrict a word to its first `p` characters. -/
def truncPrefix {n : ℕ} (p : ℕ) (hp : p ≤ n) (w : WordState n) : WordState p :=
  fun i => w ⟨i, by omega⟩




/-! ## Section 8: Berggren Tree Linking Map

We connect the word state space to concrete Berggren triple evaluation.
-/

/-- Convert a word state to a list for evaluation. -/
def wordStateToList {n : ℕ} (w : WordState n) : List (Fin 3) :=
  List.ofFn w


/-- The Berggren triple associated to a word state. -/
def berggrenTriple {n : ℕ} (w : WordState n) : ℤ × ℤ × ℤ :=
  berggrenEval (wordStateToList w)



/-! ## Section 9: Main Theorem Package -/



end BerggrenHecke


