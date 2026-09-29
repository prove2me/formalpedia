-- Prove2me | solution 1 for PadicBerggren.tree_collision_nullCone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:43.938676+00:00
-- url     : https://prove2.me/submissions/506676da-aec4-4dbf-8ea6-512aef48e07e

-- Sol generated from Geometry/PadicBerggrenNullCone.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Definitions.Def_Geometry_PadicBerggrenNullCone
import Theorems.Thm_PadicBerggren_card_nullCone_fiber
import Theorems.Thm_PadicBerggren_lorentz_wordMat

/-!
# The size of the p-adic Berggren null cone

`Catalog/Geometry/PadicBerggrenDynamics.lean` sets up the three Berggren (Barning–Hall)
generators as a dynamical system on `(ZMod (p^k))³` preserving the Lorentz form
`q(a,b,c) = a² + b² − c²`.  Every state of that system lives on the **null cone**
`q = 0`, and the whole Berggren tree reduces into it.

This file computes the exact size of the phase space:

* `PadicBerggren.card_nullCone` : for every odd prime `p` the null cone mod `p` has
  **exactly `p²` points**.  The proof fibres the cone over the linear functional
  `w ↦ w 2 − w 0` (the "light-cone coordinate" `c − a`) and shows that *every* fibre —
  including the degenerate one over `0` — has exactly `p` points.  This is the counting
  incarnation of the fact that `q` is a nondegenerate isotropic ternary form.
* `PadicBerggren.card_nullCone_nonzero` : `p² − 1` nonzero null vectors, i.e. `p + 1`
  projective null points each carrying `p − 1` nonzero vectors.
* `PadicBerggren.tree_collision_nullCone` : since the whole depth-`d` tree lands inside the
  null cone, two distinct words already collide mod `p` as soon as `3^d > p²`.  This is a
  quadratic (in `p`) obstruction, far stronger than the naive cubic bound
  `tree_collision_mod`, and it says that the reduction of the boundary of the tree has
  "box dimension at most 2": the tree cannot inject into any single finite level.
-/

open PadicBerggren

open Matrix Finset

variable (p : ℕ) [Fact p.Prime]






/-- **The null cone mod an odd prime has exactly `p²` points.**  This is the exact size of the
phase space of the reduced Berggren dynamical system. -/
theorem card_nullCone (hp : p ≠ 2) : (nullConeFinset p).card = p ^ 2 := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun w : Fin 3 → ZMod p => w 2 - w 0) (s := nullConeFinset p)
    (t := (univ : Finset (ZMod p))) (fun x _ => mem_univ _)
  rw [hfib, Finset.sum_congr rfl (fun u _ => card_nullCone_fiber p hp u),
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, sq]





open PadicBerggren in
theorem solution(d : ℕ) (hp : p ≠ 2) (h : p ^ 2 < 3 ^ d) :
    ∃ w₁ w₂ : Fin d → Fin 3, w₁ ≠ w₂ ∧
      wordMat (ZMod p) (List.ofFn w₁) *ᵥ root (ZMod p)
        = wordMat (ZMod p) (List.ofFn w₂) *ᵥ root (ZMod p) := by
  have hcard : (nullConeFinset p).card < (univ : Finset (Fin d → Fin 3)).card := by
    rw [card_nullCone p hp, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    exact h
  have hmaps : ∀ w : Fin d → Fin 3, w ∈ (univ : Finset (Fin d → Fin 3)) →
      wordMat (ZMod p) (List.ofFn w) *ᵥ root (ZMod p) ∈ nullConeFinset p := by
    intro w _
    simp only [nullConeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lorentz_wordMat (R := ZMod p) (List.ofFn w)
  obtain ⟨w₁, -, w₂, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  exact ⟨w₁, w₂, hne, heq⟩
