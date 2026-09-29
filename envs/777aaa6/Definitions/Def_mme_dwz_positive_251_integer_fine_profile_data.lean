-- Prove2me | Definitions.Def_mme_dwz_positive_251_integer_fine_profile_data
-- name    : mme_dwz_positive_251_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T16:50:05.913884+00:00
-- url     : https://prove2.me/theorems/87e3bec0-87a2-447f-bc27-cdf5ce5975db
-- title:
--   Concrete six-region integer fine profiles for the DWZ (2,5,1) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(2,5,1)$ component at $q=5$. It uses the published object-161 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 6 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here.
-- source:
--   Released q=5 fourth-power certificate (object 161), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_251_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ251Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![2, 5, 1], ![5, 2, 1], ![5, 1, 2], ![1, 5, 2], ![1, 2, 5], ![2, 1, 5]]
def shape : Fin 6 → Fin 6 → Fin 3 → Fin 5 := ![![![0, 3, 1], ![0, 4, 0], ![1, 2, 1], ![1, 3, 0], ![2, 1, 1], ![2, 2, 0]], ![![3, 0, 1], ![4, 0, 0], ![2, 1, 1], ![3, 1, 0], ![1, 2, 1], ![2, 2, 0]], ![![3, 1, 0], ![4, 0, 0], ![2, 1, 1], ![3, 0, 1], ![1, 1, 2], ![2, 0, 2]], ![![1, 3, 0], ![0, 4, 0], ![1, 2, 1], ![0, 3, 1], ![1, 1, 2], ![0, 2, 2]], ![![1, 0, 3], ![0, 0, 4], ![1, 1, 2], ![0, 1, 3], ![1, 2, 1], ![0, 2, 2]], ![![0, 1, 3], ![0, 0, 4], ![1, 1, 2], ![1, 0, 3], ![2, 1, 1], ![2, 0, 2]]]
def alphaCount : Fin 3 → Fin 6 → ℕ := ![![175185676961166, 7269091611451, 317545231427929, 317545231426810, 7269091611518, 175185676961126], ![175670124978831, 6971708974157, 317358166048026, 317358166048900, 6971708974499, 175670124975587], ![164410706128284, 168944575476521, 166644718395196, 166644718395196, 168944575476519, 164410706128284]]
def denominator : ℕ := 199999999999999800000000000000000000000000000
def profileCount : Fin 11 → Fin 9 → ℕ :=
  ![![199999999999999800000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 99999999999999900000000000000000000000000000, 0, 99999999999999900000000000000000000000000000, 0], ![0, 99999999999999900000000000000000000000000000, 0, 99999999999999900000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 199999999999999800000000000000000000000000000], ![0, 0, 4199999999999995800000000000000000000000000, 0, 191599999999999808400000000000000000000000000, 0, 4199999999999995800000000000000000000000000, 0, 0], ![0, 0, 7406830183747792593169816252200000000000000, 0, 185186339538453814813660461546000000000000000, 0, 7406830277798192593169722201800000000000000, 0, 0], ![0, 0, 7406830277798192593169722201800000000000000, 0, 185186339538453814813660461546000000000000000, 0, 7406830183747792593169816252200000000000000, 0, 0], ![0, 0, 9914383171844609174305492026761780373349, 0, 199980171233656110781651389015946476439253302, 0, 9914383171844609174305492026761780373349, 0, 0], ![0, 0, 7525789686141992474210313858000000000000000, 0, 184948420796412015051579203587800000000000000, 0, 7525789517445792474210482554200000000000000, 0, 0], ![0, 0, 7525789517445792474210482554200000000000000, 0, 184948420796412015051579203587800000000000000, 0, 7525789686141992474210313858000000000000000, 0, 0], ![0, 0, 66666666631841400000000000000000000000000000, 0, 66666666736317000000000000000000000000000000, 0, 66666666631841400000000000000000000000000000, 0, 0]]
def profileIndex : Fin 6 → Fin 6 → Fin 3 → Fin 11 :=
  ![![![0, 1, 2], ![0, 3, 0], ![2, 4, 2], ![2, 1, 0], ![4, 2, 2], ![5, 6, 0]], ![![1, 0, 2], ![3, 0, 0], ![4, 2, 2], ![1, 2, 0], ![2, 4, 2], ![6, 5, 0]], ![![1, 2, 0], ![3, 0, 0], ![4, 2, 2], ![1, 0, 2], ![2, 2, 7], ![8, 0, 9]], ![![2, 1, 0], ![0, 3, 0], ![2, 4, 2], ![0, 1, 2], ![2, 2, 7], ![0, 8, 9]], ![![2, 0, 1], ![0, 0, 3], ![2, 2, 7], ![0, 2, 1], ![2, 4, 2], ![0, 10, 10]], ![![0, 2, 1], ![0, 0, 3], ![2, 2, 7], ![2, 0, 1], ![4, 2, 2], ![10, 0, 10]]]

def fineCount (r : Fin 6) (j : Fin 6) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 6) (j : Fin 6) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 6) : Fin 6 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent251.regionalWeight (region r)
def n (r : Fin 6) : ℕ := weightCount r * 1000000000000000 * denominator
noncomputable def m (r : Fin 6) (c : RecursiveThinSplit.Split 4 (parent r)) : ℕ :=
  weightCount r * alphaCount (region r) ((splitEquiv r).symm c) * denominator
noncomputable def mu (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  let j := (splitEquiv c.1).symm c.2
  weightCount c.1 * (alphaCount (region c.1) j + alphaCount (region c.1) (Fin.rev j)) *
    fineCount c.1 j i (wordEquiv.symm w)
def totalCount : ℕ := 2000000000000002000000000000000 * denominator

/-- Normalized formulas used to certify the entropy of the same integer data. -/
def weight (r : Fin 6) : ℚ := (weightCount r : ℚ) / 2000000000000002
def alpha (r : Fin 6) (j : Fin 6) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 6) (j : Fin 6) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 6) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 6, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 6) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 6, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 6) (j : Fin 6) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 6) (s : Fin 11) (w : Fin 9) : ℚ :=
  ∑ j : Fin 6,
    if (if boundary i r j then j.val else 6 + (shape r j (yzMode i)).val) = s.val
    then (alpha r j + alpha r (Fin.rev j)) * beta r j (yzMode i) w else 0

noncomputable def ratEntropy {t : ℕ} (p : Fin t → ℚ) : ℝ :=
  ∑ j, Real.negMulLog (p j : ℝ)
noncomputable def ratMassEntropy {t : ℕ} (p : Fin t → ℚ) : ℝ :=
  ratEntropy p - Real.negMulLog ((∑ j, p j : ℚ) : ℝ)
noncomputable def coarseRate : ℝ :=
  ∑ r, (weight r : ℝ) * ratEntropy (coarse r 0)
noncomputable def parentRate (i : Fin 3) : ℝ :=
  ∑ r, (weight r : ℝ) * ∑ a, ∑ b, Real.negMulLog (jointWord r i a b : ℝ)
noncomputable def compatibilityRate (i : Fin 2) : ℝ :=
  ∑ r, (weight r : ℝ) * ∑ s, ratMassEntropy (partMass i r s)
noncomputable def explicitRate : ℝ :=
  min coarseRate (min (parentRate 1 - compatibilityRate 0) (parentRate 2 - compatibilityRate 1))

end MME.DWZ251Fine


