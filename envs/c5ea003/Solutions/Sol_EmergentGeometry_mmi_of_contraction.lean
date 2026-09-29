-- Prove2me | solution 1 for EmergentGeometry.mmi_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:01:04.843179+00:00
-- url     : https://prove2.me/submissions/2023f6be-bde5-4931-8e6d-5edf239bfeff

-- Sol generated from Novelty/HolographicContractionCalculus.lean
import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Definitions.Def_Novelty_HolographicContractionCalculus
import Definitions.Def_Novelty_HolographicCyclicInequality
import Theorems.Thm_EmergentGeometry_entropy_le_of_contraction

/-!
# A calculus of holographic entropy inequalities

Monogamy of mutual information and the five-party cyclic inequality were each
proved by exhibiting a Boolean recombination rule for minimal surfaces.  This
file isolates the mechanism as a single structure and a single theorem, turning
"find a holographic entropy inequality" into "find a contraction map".

A `ContractionMap k m` is a map `χ : Bool^k → Bool^m` that does not increase
Hamming distance.  Given `k` boundary regions `A i` and `m` boundary regions
`B j` whose boundary indicator patterns are related by `χ`, the theorem
`entropy_le_of_contraction` yields

`∑ j S(B j) ≤ ∑ i S(A i)`.

Subadditivity, strong subadditivity and monogamy are all recovered as
instances (`subadditive_of_contraction`, `ssa_of_contraction`,
`mmi_of_contraction`), and `entropy_cyclic5` of
`Novelty.HolographicCyclicInequality` is the instance attached to the cyclic
rule `cyc`.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V]


variable [DecidableEq V]


/-! ## The classical inequalities as contraction maps -/








open EmergentGeometry in
theorem solution(M : HoloModel V) (A B C : Region V)
    (hAB : ∀ v, A v = true → B v = false)
    (hBC : ∀ v, B v = true → C v = false)
    (hAC : ∀ v, A v = true → C v = false) :
    entropy M A + entropy M B + entropy M C
        + entropy M (fun v => A v || B v || C v)
      ≤ entropy M (fun v => A v || B v) + entropy M (fun v => B v || C v)
        + entropy M (fun v => A v || C v) := by
  have h := entropy_le_of_contraction M
    ![fun v => A v || B v, fun v => B v || C v, fun v => A v || C v]
    ![B, A, C, fun v => A v || B v || C v] minorityMap
    (by
      intro v _ j
      have h1 := hAB v
      have h2 := hBC v
      have h3 := hAC v
      fin_cases j <;>
        simp only [minorityMap, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
        cases hA' : A v <;> cases hB' : B v <;> cases hC' : C v <;> simp_all)
  simp only [Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three] at h
  linarith
