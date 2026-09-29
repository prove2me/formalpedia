-- Prove2me | solution 1 for Cryptography.IsogenySIDH.montgomery_models_card_le_six
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:47:45.207992+00:00
-- url     : https://prove2.me/submissions/572815b6-c0c5-4150-bc52-bffebfab5698

-- Sol generated from Cryptography/IsogenySIDH/ModularTwoIsogeny.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
/-
# The radical Montgomery step is a genuine edge of the 2-isogeny graph

`RadicalMontgomeryFormula` produced an explicit rational map from `E_A` to a
generalized Montgomery curve with parameter `radTwoParam A α = (A+6)/(2α)`,
`α² = A + 2`.  That is a *local* verification: the formulas transport points.
This file supplies the *global* certificate that the construction really is a
2-isogeny, by checking it against the classical modular polynomial `Φ₂`.

The main results are:

* `jMont_radTwoParam` — the `j`-invariant of the target is
  `jQuot A = 16 (A²+12)³ / (A²-4)²`.  Remarkably the radical `α` cancels: the
  target `j` is a *rational* function of `A`.
* `jMont_model_independent` — the three Montgomery renormalisations of the
  quotient curve (obtained by moving each of its three two-torsion points to
  the origin, using the three radicals `√(A+2)`, `√(2-A)`, `√(A²-4)`) all have
  the same `j`-invariant `jQuot A`.  So the radical step is independent of the
  chosen model and of the sign of the radical.
* `modPoly2_jMont_jQuot` and `modPoly2_radical_step` — the pair
  `(j(E_A), j(E_{A'}))` is a zero of the level-2 modular polynomial `Φ₂`.  This
  is the definitive certificate of 2-isogeny, proved as a polynomial identity
  of degree 54 in `A`.
* `radChain_isTwoIsogenyPath` — an admissible radical walk traces a path in the
  2-isogeny graph, by induction along the walk.
* `two_isogeny_neighbours_card_le_three` — `Φ₂` is monic of degree three in each
  variable, so every vertex of the 2-isogeny graph has at most three neighbours;
  this bounds the branching of a radical walk and is what makes the walk a walk
  on a cubic (Ramanujan) graph.
-/

open Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## `j`-invariants -/





/-! ## The three Montgomery models of the quotient -/








/-! ## The level-2 modular polynomial -/






/-! ## Radical walks are paths in the 2-isogeny graph -/






/-! ## Degree bound: the 2-isogeny graph is cubic -/






/-! ## How many Montgomery models does one `j`-invariant have? -/


theorem montModelPoly_eval (j A : K) :
    (montModelPoly j).eval A = 256 * (A ^ 2 - 3) ^ 3 - j * (A ^ 2 - 4) := by
  simp only [montModelPoly, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem montModelPoly_natDegree (htwo : (2 : K) ≠ 0) (j : K) :
    (montModelPoly j).natDegree = 6 := by
  have h256 : (256 : K) ≠ 0 := by
    have h : (256 : K) = 2 ^ 8 := by norm_num
    rw [h]; exact pow_ne_zero 8 htwo
  unfold montModelPoly
  compute_degree!

theorem montModelPoly_ne_zero (htwo : (2 : K) ≠ 0) (j : K) : montModelPoly j ≠ 0 := by
  intro h
  have hdeg := montModelPoly_natDegree htwo j
  rw [h] at hdeg
  simp at hdeg

/-- A Montgomery parameter is a root of `montModelPoly j` exactly when its
`j`-invariant is `j`. -/
theorem jMont_eq_iff_isRoot {A j : K} (hd : A ^ 2 - 4 ≠ 0) :
    jMont A = j ↔ (montModelPoly j).IsRoot A := by
  rw [IsRoot, montModelPoly_eval, jMont, div_eq_iff hd]
  constructor <;> intro h <;> linear_combination h



open Cryptography.IsogenySIDH in
theorem solution[DecidableEq K] (htwo : (2 : K) ≠ 0) (j : K)
    (S : Finset K) (hS : ∀ A ∈ S, A ^ 2 - 4 ≠ 0 ∧ jMont A = j) : S.card ≤ 6 := by
  have hsub : S ⊆ (montModelPoly j).roots.toFinset := by
    intro A hA
    obtain ⟨hd, hj⟩ := hS A hA
    rw [Multiset.mem_toFinset, mem_roots (montModelPoly_ne_zero htwo j)]
    exact (jMont_eq_iff_isRoot hd).mp hj
  calc S.card ≤ (montModelPoly j).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (montModelPoly j).roots := Multiset.toFinset_card_le _
    _ ≤ (montModelPoly j).natDegree := card_roots' _
    _ = 6 := montModelPoly_natDegree htwo j
