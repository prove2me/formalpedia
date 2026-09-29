-- Prove2me | Definitions.Def_Geometry_ToricCode_Basic
-- name    : Geometry_ToricCode_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:19:12.659433+00:00
-- url     : https://prove2.me/theorems/18b429a4-e895-48ba-b09a-96cac05b47f8
-- title:
--   Aether Catalog definitions — Geometry_ToricCode_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ToricCode.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ToricCode/Basic.lean by skeleton subtraction
import Mathlib

/-!
# The `M × N` torus surface code: cellular chain complex

This file builds the *geometric* object requested by target 3 of the previous
research cycle: the cellular chain complex of the standard square-grid
cellulation of the two-dimensional torus `(ℤ/M) × (ℤ/N)`, over the binary field
`𝔽₂`.

* vertices  `Vert M N = ZMod M × ZMod N`                      (`MN` of them),
* edges     `Edge M N = Bool × ZMod M × ZMod N`               (`2MN` of them):
  the edge `(false, u)` joins `u` to `u + (1,0)`, the edge `(true, u)` joins `u`
  to `u + (0,1)`,
* faces     `Face M N = ZMod M × ZMod N`                      (`MN` of them):
  the face `f` is the unit square with corners `f, f+(1,0), f+(0,1), f+(1,1)`.

The two boundary matrices are `d1 : Vert × Edge` and `d2 : Edge × Face`.  The
main content of this file is a set of *explicit pointwise formulas* for the four
maps `d1 *ᵥ ·`, `d2 *ᵥ ·`, `d1ᵀ *ᵥ ·`, `d2ᵀ *ᵥ ·`, together with the chain
condition `d1 ∘ d2 = 0`.  Everything downstream is proved from these formulas,
never by unfolding the matrices again.
-/

open Matrix

namespace ToricCode

/-- The binary field. -/
abbrev F2 := ZMod 2

variable (M N : ℕ) [NeZero M] [NeZero N]

/-- Vertices (`0`-cells) of the torus grid. -/
abbrev Vert := ZMod M × ZMod N

/-- Edges (`1`-cells, i.e. physical qubits).  `(false, u)` is the horizontal
edge based at `u`, `(true, u)` the vertical one. -/
abbrev Edge := Bool × ZMod M × ZMod N

/-- Faces (`2`-cells) of the torus grid. -/
abbrev Face := ZMod M × ZMod N

/-- The lattice step associated to an edge direction. -/
def step (b : Bool) : ZMod M × ZMod N := cond b (0, 1) (1, 0)

omit [NeZero M] [NeZero N] in @[simp] lemma step_false : step M N false = (1, 0) := rfl
omit [NeZero M] [NeZero N] in @[simp] lemma step_true : step M N true = (0, 1) := rfl


/-- The `1`-boundary matrix: an edge is sent to the sum of its two endpoints. -/
def d1 : Matrix (Vert M N) (Edge M N) F2 :=
  fun v e => (if v = e.2 then 1 else 0) + (if v = e.2 + step M N e.1 then 1 else 0)

/-- The `2`-boundary matrix: a face is sent to the sum of its four sides. -/
def d2 : Matrix (Edge M N) (Face M N) F2 :=
  fun e f => (if e.2 = f then 1 else 0) + (if e.2 = f + step M N (!e.1) then 1 else 0)

/-! ### Pointwise formulas -/

private lemma sum_two_ind (s v : ZMod M × ZMod N) (f : (ZMod M × ZMod N) → F2) :
    ∑ u : ZMod M × ZMod N,
        ((if v = u then (1:F2) else 0) + (if v = u + s then 1 else 0)) * f u
      = f v + f (v - s) := by
  classical
  have h : ∀ u : ZMod M × ZMod N,
      ((if v = u then (1:F2) else 0) + (if v = u + s then 1 else 0)) * f u
        = (if v = u then f u else 0) + (if v - s = u then f u else 0) := by
    intro u
    simp only [add_mul, ite_mul, one_mul, zero_mul]
    congr 2
    simp only [eq_iff_iff]
    constructor
    · intro h; rw [h]; ring
    · intro h; rw [← h]; ring
  rw [Finset.sum_congr rfl (fun u _ => h u), Finset.sum_add_distrib]
  simp


/-- The cellular boundary of a `1`-chain at a vertex: the sum of the four
incident edges. -/
lemma d1_mulVec (z : Edge M N → F2) (v : Vert M N) :
    (d1 M N *ᵥ z) v = z (false, v) + z (false, v - (1, 0))
      + (z (true, v) + z (true, v - (0, 1))) := by
  classical
  simp only [Matrix.mulVec, d1, dotProduct]
  rw [Fintype.sum_prod_type, Fintype.sum_bool,
      sum_two_ind M N (step M N false) v (fun u => z (false, u)),
      sum_two_ind M N (step M N true) v (fun u => z (true, u))]
  simp only [step_false, step_true]
  ring

/-- The cellular boundary of a `2`-chain, evaluated on an edge. -/
lemma d2_mulVec (g : Face M N → F2) (b : Bool) (u : ZMod M × ZMod N) :
    (d2 M N *ᵥ g) (b, u) = g u + g (u - step M N (!b)) := by
  classical
  simp only [Matrix.mulVec, d2, dotProduct]
  exact sum_two_ind M N (step M N (!b)) u g



/-! ### The chain condition -/

private lemma f2_four (a b c d : F2) : a + b + (c + d) + (a + c + (b + d)) = 0 := by
  have h : ∀ x : F2, x + x = 0 := by decide
  linear_combination (h a) + (h b) + (h c) + (h d)

/-- **The torus grid is a chain complex**: the boundary of a boundary vanishes. -/
theorem d1_d2_mulVec (g : Face M N → F2) : d1 M N *ᵥ (d2 M N *ᵥ g) = 0 := by
  funext v
  rw [d1_mulVec]
  simp only [d2_mulVec, Bool.not_false, Bool.not_true, step_false, step_true]
  have hcomm : v - (1, 0) - ((0:ZMod M), (1:ZMod N)) = v - (0, 1) - ((1:ZMod M), (0:ZMod N)) := by
    obtain ⟨a, b⟩ := v
    simp only [Prod.mk_sub_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [hcomm]
  simpa using f2_four (g v) (g (v - (0,1))) (g (v - (1,0))) (g (v - (0,1) - (1,0)))


/-! ### Basic counting -/




/-! ### Kernels of the two coboundary operators are the constants -/


end ToricCode


