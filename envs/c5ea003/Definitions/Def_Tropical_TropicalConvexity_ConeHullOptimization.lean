-- Prove2me | Definitions.Def_Tropical_TropicalConvexity_ConeHullOptimization
-- name    : Tropical_TropicalConvexity_ConeHullOptimization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:13.430381+00:00
-- url     : https://prove2.me/theorems/de5fe4b8-7c75-4573-9ae4-a6b79698c0b8
-- title:
--   Aether Catalog definitions — Tropical_TropicalConvexity_ConeHullOptimization
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalConvexity.ConeHullOptimization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalConvexity/ConeHullOptimization.lean by skeleton subtraction
import Mathlib

/-!
# Tropical cone hulls, Carathéodory number `d`, and max-plus residuation

This file complements the tropical Helly theory with the two other pillars of
tropical convexity: the **Carathéodory number** of tropical cones in `ℝ^d`
(which is `d`, one better than the affine normalized bound `d + 1`), and the
**optimization side**: the residuation (Galois) correspondence for max-plus
linear systems, giving the greatest subsolution of `A ⊗ x ≤ b` together with a
complete solvability criterion for `A ⊗ x = b`.

## Main results

* `TropicalConeHull.tropical_caratheodory_cone` — Carathéodory number `d`.
* `TropicalConeHull.caratheodory_cone_sharp` — the bound `d` cannot be improved.
* `TropicalConeHull.colorful_caratheodory` — colourful Carathéodory theorem.
* `TropicalConeHull.dependence_of_helly` — the converse implication
  "tropical Helly ⇒ tropical Cramer dependence", so that the Helly theorem of
  `HellyNumber.lean` and the dependence theorem behind it are *equivalent*.
* `TropicalResiduation.mulVec_le_iff_le_resid` — the residuation Galois
  connection for max-plus linear inequalities.
* `TropicalResiduation.tropical_solvable_iff` — `A ⊗ x = b` is solvable iff the
  canonical candidate `resid A b` solves it (Cuninghame-Green's principal
  solution): an `O(mn)` decision procedure for max-plus linear systems.
-/

open Finset

namespace TropicalConeHull

variable {d : ℕ} {ι : Type*}

/-- The **tropical cone hull** of a finite family of points: all max-plus
combinations `z i = max_{k ∈ F} (lam k + p k i)` with arbitrary real weights. -/
def tropConeHull (p : ι → Fin d → ℝ) (F : Finset ι) : Set (Fin d → ℝ) :=
  {z | ∃ (lam : ι → ℝ) (hF : F.Nonempty),
    ∀ i, z i = F.sup' hF (fun k => lam k + p k i)}





/-! ## The tropical Helly property is *equivalent* to tropical dependence

`HellyNumber.lean` proves the implication "Cramer dependence ⇒ tropical Helly".
Here we close the loop: the Helly property, taken as a hypothesis, forces
`d + 1` points of `ℝ^d` to be tropically dependent.  So the two statements are
two faces of the same phenomenon. -/

/-- Tropical cone (max-plus submodule), as in `HellyNumber.lean`. -/
def IsTropCone (S : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ s t : ℝ, (fun i => max (s + x i) (t + y i)) ∈ S





end TropicalConeHull

namespace TropicalResiduation

variable {m n : ℕ}

/-- Max-plus matrix–vector product `(A ⊗ x) i = max_j (A i j + x j)`. -/
noncomputable def mulVec (A : Fin (m + 1) → Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℝ)
    (i : Fin (m + 1)) : ℝ :=
  univ.sup' univ_nonempty (fun j => A i j + x j)

/-- The **residuated vector** `A ♯ b`, i.e. `(A ♯ b) j = min_i (b i - A i j)`. -/
noncomputable def resid (A : Fin (m + 1) → Fin (n + 1) → ℝ) (b : Fin (m + 1) → ℝ)
    (j : Fin (n + 1)) : ℝ :=
  univ.inf' univ_nonempty (fun i => b i - A i j)






end TropicalResiduation


