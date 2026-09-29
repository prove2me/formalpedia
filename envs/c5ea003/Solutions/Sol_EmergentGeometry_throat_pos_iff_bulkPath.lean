-- Prove2me | solution 1 for EmergentGeometry.throat_pos_iff_bulkPath
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:42:53.418707+00:00
-- url     : https://prove2.me/submissions/92ddc635-2754-4eb9-a7b7-a1b3eac54369

-- Sol generated from Novelty/EREPRThroatCapacity.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_exists_min_throat_surface
import Theorems.Thm_EmergentGeometry_throat_le_of_separates
import Theorems.Thm_EmergentGeometry_throat_nonneg
import Theorems.Thm_EmergentGeometry_weight_eq_zero_of_cutWeight_eq_zero

/-!
# Throat capacity of an Einstein–Rosen bridge and the `I ≤ 2 E_W` bound

This file adds a genuinely *geometric* observable to the min-cut model of
`Novelty.EmergentGeometryEntropyCone`: the **throat capacity**

  `throat G A B = min { area(σ) : σ ⊇ A, σ ∩ B = ∅ }`,

the smallest bulk surface that has to be cut in order to disconnect the bulk
region `A` from the bulk region `B`.  Unlike the entropy `S(A)` this is *not*
constrained to be homologous to a boundary region: it measures the cross-section
of the Einstein–Rosen bridge joining `A` to `B` (the discrete analogue of the
entanglement wedge cross-section `E_W`).

Main results:

* `cutWeight_eq_zero_of_closed`, `weight_eq_zero_of_cutWeight_eq_zero`:
  a bulk surface has zero area iff no positive-weight edge crosses it.
* `throat_pos_iff_bulkPath` : **the throat capacity of a pair of cells is
  positive exactly when an Einstein–Rosen bridge joins them.**  Geometric
  connectivity is detected by a single real number.
* `mutualInfo_le_two_throat` : **`I(A:B) ≤ 2 · throat(A,B)`**, the toy-model
  form of the holographic inequality `I(A:B) ≤ 2 E_W(A:B)`: entanglement between
  two boundary regions is bounded by the cross-section of the bridge that
  connects them.  Its combinatorial engine is the new pointwise Boolean
  inequality `sepBit_split`.
* `throat_le_entropy`, `throat_sandwich` : `I(A:B)/2 ≤ throat(A,B) ≤ min(S A, S B)`.
* `ER_EPR_throat` : positive mutual information of two boundary cells forces a
  positive-capacity Einstein–Rosen bridge between them — ER = EPR with a
  quantitative bound, strengthening `bridge_of_mutualInfo_pos`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  In holography the entanglement wedge cross-section
`E_W` obeys `E_W ≥ I/2`.  If the slogan "ER=EPR" is to have content beyond mere
connectivity, the *width* of the bridge should bound the *amount* of
entanglement, not just its (non)vanishing.

EXPERIMENT (Experimenter).  We defined `throat` as an unconstrained min-cut and
looked for a recombination of Boolean regions realising the bound.  The winning
combination splits the minimal surface `g` of `A ∪ B` along the minimal
separating surface `σ`: `X = σ ∧ g` is homologous to `A`, `Y = ¬σ ∧ g` to `B`.
The needed pointwise fact is `sepBit_split`, i.e.
`sep(a∧b) + sep(¬a∧b) ≤ sep(b) + 2 sep(a)`, a 16-case Boolean identity; note the
factor `2` is necessary (take `a₁ = true, a₂ = false, b₁ = b₂ = true`, where the
left side is `2` and `sep b = 0`).

ANALYSIS (Analyst).  The bound is *tight*: for a single throat of weight `w`
between two boundary cells one has `throat = w` and `I = 2w`.  Combined with
`throat ≤ min(S A, S B)` we obtain a two-sided sandwich, so in the toy model the
bridge cross-section is squeezed between half the mutual information and the
entropies of its two mouths.

CRITIQUE (Critic).  `throat` is a `dite` over a possibly empty family; all
statements that use its minimality carry the disjointness hypothesis that makes
the family nonempty, and none of them is vacuous (`pairModel_throat` exhibits a
model where every hypothesis holds and the value is nonzero).
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Surfaces separating two bulk regions -/


private lemma bool_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h













/-! ## Monotonicity in the amount of entanglement -/



/-! ## Zero-area surfaces and bulk connectivity -/

omit [DecidableEq V] in
/-- A bulk surface whose two sides are joined by no positive weight has zero
area. -/
lemma cutWeight_eq_zero_of_closed (G : BulkGraph V) (f : Region V)
    (h : ∀ x y, f x = true → f y = false → G.weight x y = 0) :
    cutWeight G f = 0 := by
  have hterm : ∀ x y : V, (sepBit (f x) (f y) : ℝ) * G.weight x y = 0 := by
    intro x y
    cases hx : f x <;> cases hy : f y
    · simp [sepBit]
    · rw [(G.weight_symm x y).trans (h y x hy hx)]; ring
    · rw [h x y hx hy]; ring
    · simp [sepBit]
  simp [cutWeight, hterm]


omit [DecidableEq V] in
/-- A bulk region closed under positive-weight steps contains everything
reachable from it. -/
lemma mem_of_bulkPath {G : BulkGraph V} {f : Region V}
    (hcl : ∀ x y, f x = true → f y = false → G.weight x y = 0) {u v : V}
    (hp : BulkPath G u v) (hu : f u = true) : f v = true := by
  induction hp with
  | refl => exact hu
  | tail _ hstep ih =>
      rename_i b c _
      have hb : f b = true := ih
      by_contra hc
      have hc' : f c = false := bool_false_of_ne_true hc
      have := hcl b c hb hc'
      exact absurd this (ne_of_gt hstep)


/-! ## The bound `I(A:B) ≤ 2 · throat(A,B)` -/







/-! ## Sharpness: a single throat saturates the bound -/



open EmergentGeometry in
theorem solution(G : BulkGraph V) {u v : V} (huv : u ≠ v) :
    0 < throat G (single u) (single v) ↔ BulkPath G u v := by
  have hdisj : Disj (single u) (single v) := by
    intro x hx
    simp only [single, decide_eq_true_eq] at hx ⊢
    simp [hx, huv]
  constructor
  · intro hpos
    by_contra hnp
    classical
    -- the set of cells reachable from `u` is a zero-area separating surface
    set R : Region V := fun x => if BulkPath G u x then true else false with hR
    have hRtrue : ∀ x, R x = true ↔ BulkPath G u x := by
      intro x
      by_cases h : BulkPath G u x <;> simp [hR, h]
    have hRu : R u = true := (hRtrue u).2 Relation.ReflTransGen.refl
    have hclosed : ∀ x y, R x = true → R y = false → G.weight x y = 0 := by
      intro x y hx hy
      by_contra hw
      have hpos' : 0 < G.weight x y := lt_of_le_of_ne (G.weight_nonneg x y) (Ne.symm hw)
      have hRy : R y = true := (hRtrue y).2 (((hRtrue x).1 hx).tail hpos')
      rw [hRy] at hy
      exact Bool.noConfusion hy
    have hsep : Separates (single u) (single v) R := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · simp only [single, decide_eq_true_eq] at hx
        rw [hx]; exact hRu
      · simp only [single, decide_eq_true_eq] at hx
        subst hx
        exact bool_false_of_ne_true fun h => hnp ((hRtrue x).1 h)
    have := throat_le_of_separates (G := G) hsep
    rw [cutWeight_eq_zero_of_closed G R hclosed] at this
    linarith
  · intro hpath
    rcases lt_or_eq_of_le (throat_nonneg G (single u) (single v)) with h | h
    · exact h
    · exfalso
      obtain ⟨f, hf, hval⟩ := exists_min_throat_surface G hdisj
      have hcut : cutWeight G f = 0 := by rw [← hval, ← h]
      have hfu : f u = true := hf.1 u (by simp [single])
      have hfv : f v = false := hf.2 v (by simp [single])
      have hcl : ∀ x y, f x = true → f y = false → G.weight x y = 0 :=
        fun x y hx hy => weight_eq_zero_of_cutWeight_eq_zero hcut hx hy
      rw [mem_of_bulkPath hcl hpath hfu] at hfv
      exact Bool.noConfusion hfv
