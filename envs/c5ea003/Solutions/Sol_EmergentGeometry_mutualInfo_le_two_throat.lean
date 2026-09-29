-- Prove2me | solution 1 for EmergentGeometry.mutualInfo_le_two_throat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:39:29.719508+00:00
-- url     : https://prove2.me/submissions/b6ba2cb2-67fb-4164-9738-d362396ec9c2

-- Sol generated from Novelty/EREPRThroatCapacity.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRThroatCapacity
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_cutWeight_comb
import Theorems.Thm_EmergentGeometry_entropy_le_of_admissible
import Theorems.Thm_EmergentGeometry_exists_min_throat_surface
import Theorems.Thm_EmergentGeometry_exists_minimal_surface

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





/-! ## The bound `I(A:B) ≤ 2 · throat(A,B)` -/

/-- **Pointwise splitting inequality.**  Splitting a region `b` along a region
`a` costs at most the separations of `b` plus twice those of `a`.  The factor
`2` is sharp (`a₁ = true, a₂ = false, b₁ = b₂ = true`). -/
lemma sepBit_split (a₁ a₂ b₁ b₂ : Bool) :
    sepBit (a₁ && b₁) (a₂ && b₂) + sepBit (!a₁ && b₁) (!a₂ && b₂)
      ≤ sepBit b₁ b₂ + 2 * sepBit a₁ a₂ := by
  revert a₁ a₂ b₁ b₂; decide

omit [DecidableEq V] in
/-- Areas version of the splitting inequality: cutting a region `g` into its
parts inside and outside `σ` costs at most `area(g) + 2 · area(σ)`. -/
theorem cutWeight_split (G : BulkGraph V) (σ g : Region V) :
    cutWeight G (fun v => σ v && g v) + cutWeight G (fun v => !(σ v) && g v)
      ≤ cutWeight G g + 2 * cutWeight G σ := by
  have h := cutWeight_comb G ![g, σ, σ]
    ![fun v => σ v && g v, fun v => !(σ v) && g v]
    (by
      intro u v _
      simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      have := sepBit_split (σ u) (σ v) (g u) (g v)
      omega)
  simpa [Fin.sum_univ_two, Fin.sum_univ_three, two_mul, add_assoc] using h





/-! ## Sharpness: a single throat saturates the bound -/



open EmergentGeometry in
theorem solution(M : HoloModel V) {A B : Region V} (hAB : Disj A B) :
    mutualInfo M A B ≤ 2 * throat M.toBulkGraph A B := by
  obtain ⟨σ, hσ, hσval⟩ := exists_min_throat_surface M.toBulkGraph hAB
  obtain ⟨g, hg, hgval⟩ := exists_minimal_surface M (fun v => A v || B v)
  have hX : Admissible M A (fun v => σ v && g v) := by
    intro v hv
    have hgv : g v = (A v || B v) := hg v hv
    show (σ v && g v) = A v
    rw [hgv]
    by_cases hA : A v = true
    · simp [hσ.1 v hA, hA]
    · have hA' : A v = false := bool_false_of_ne_true hA
      by_cases hB : B v = true
      · simp [hσ.2 v hB, hA']
      · have hB' : B v = false := bool_false_of_ne_true hB
        simp [hA', hB']
  have hY : Admissible M B (fun v => !(σ v) && g v) := by
    intro v hv
    have hgv : g v = (A v || B v) := hg v hv
    show (!(σ v) && g v) = B v
    rw [hgv]
    by_cases hA : A v = true
    · simp [hσ.1 v hA, hAB v hA]
    · have hA' : A v = false := bool_false_of_ne_true hA
      by_cases hB : B v = true
      · simp [hσ.2 v hB, hB]
      · have hB' : B v = false := bool_false_of_ne_true hB
        simp [hA', hB']
  have e1 := entropy_le_of_admissible hX
  have e2 := entropy_le_of_admissible hY
  have hsplit := cutWeight_split M.toBulkGraph σ g
  simp only [mutualInfo]
  rw [hgval, hσval]
  linarith
