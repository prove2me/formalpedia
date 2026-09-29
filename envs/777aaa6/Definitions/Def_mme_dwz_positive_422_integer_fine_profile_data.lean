-- Prove2me | Definitions.Def_mme_dwz_positive_422_integer_fine_profile_data
-- name    : mme_dwz_positive_422_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T17:55:41.912852+00:00
-- url     : https://prove2.me/theorems/ba2196d8-0233-40f6-bb5c-c8a169d56b09
-- title:
--   Concrete six-region integer fine profiles for the DWZ (4,2,2) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(4,2,2)$ component at $q=5$. It uses the published object-171 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 9 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here. For this non-thin component the coarse branch of `explicitRate` also subtracts `penaltyRate`: the weighted gap between the public recursive maximum-entropy upper bounds of the regional parents (`witnessIndex` into `mme_dwz_fourth_rational_recursive_entropy_data`) and the entropies of the actual split distributions.
-- source:
--   Released q=5 fourth-power certificate (object 171), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_422_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ422Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![4, 2, 2], ![2, 4, 2], ![2, 2, 4], ![2, 2, 4], ![2, 4, 2], ![4, 2, 2]]
def shape : Fin 6 → Fin 9 → Fin 3 → Fin 5 := ![![![0, 2, 2], ![1, 1, 2], ![1, 2, 1], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]], ![![2, 0, 2], ![1, 1, 2], ![2, 1, 1], ![0, 2, 2], ![1, 2, 1], ![2, 2, 0], ![0, 3, 1], ![1, 3, 0], ![0, 4, 0]], ![![2, 2, 0], ![1, 2, 1], ![2, 1, 1], ![0, 2, 2], ![1, 1, 2], ![2, 0, 2], ![0, 1, 3], ![1, 0, 3], ![0, 0, 4]], ![![2, 2, 0], ![2, 1, 1], ![1, 2, 1], ![2, 0, 2], ![1, 1, 2], ![0, 2, 2], ![1, 0, 3], ![0, 1, 3], ![0, 0, 4]], ![![2, 0, 2], ![2, 1, 1], ![1, 1, 2], ![2, 2, 0], ![1, 2, 1], ![0, 2, 2], ![1, 3, 0], ![0, 3, 1], ![0, 4, 0]], ![![0, 2, 2], ![1, 2, 1], ![1, 1, 2], ![2, 2, 0], ![2, 1, 1], ![2, 0, 2], ![3, 1, 0], ![3, 0, 1], ![4, 0, 0]]]
def alphaCount : Fin 3 → Fin 9 → ℕ := ![![335248552666, 38502795200294, 40809891537010, 142318275318655, 556067587402861, 142318269827463, 40809889767587, 38502793825513, 335248567951], ![340040592232, 40657966652452, 40612704598542, 142322072499573, 552134443275677, 142322064367695, 40612704231221, 40657963204249, 340040578359], ![141162900466278, 109078568464951, 109055719146890, 90545461789706, 100309146998129, 90551015506436, 109061273146463, 109073014264175, 141162900216972]]
def denominator : ℕ := 437062937062937062937062937062500000000000000000000000000
def profileCount : Fin 12 → Fin 9 → ℕ :=
  ![![437062937062937062937062937062500000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 24156255610886800699300699300675144443689812500000000000, 0, 388750426010968531468531468531079781042520500000000000000, 0, 24156255441081730769230769230745074513789687500000000000, 0, 0], ![0, 0, 24156255441081730769230769230745074513789687500000000000, 0, 388750426010968531468531468531079781042520500000000000000, 0, 24156255610886800699300699300675144443689812500000000000, 0, 0], ![0, 218531468531468531468531468531250000000000000000000000000, 0, 218531468531468531468531468531250000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 2394945988495008221301631782871804989006722117578763373, 0, 432273045085947046494459673496756390021986555764842473254, 0, 2394945988495008221301631782871804989006722117578763373, 0, 0], ![0, 0, 9178321678321678321678321678312500000000000000000000000, 0, 418706293706293706293706293705875000000000000000000000000, 0, 9178321678321678321678321678312500000000000000000000000, 0, 0], ![0, 0, 19048878828137693874053653312500000000000000000000000000, 0, 398965179427222864000144462187500000000000000000000000000, 0, 19048878807576505062864821562500000000000000000000000000, 0, 0], ![0, 0, 19048878807576505062864821562500000000000000000000000000, 0, 398965179427222864000144462187500000000000000000000000000, 0, 19048878828137693874053653312500000000000000000000000000, 0, 0], ![0, 0, 16186254772176136363636363636347450108864187500000000000, 0, 404690427313055069930069930069525379502756875000000000000, 0, 16186254977705856643356643356627170388378937500000000000, 0, 0], ![0, 0, 16186254977705856643356643356627170388378937500000000000, 0, 404690427313055069930069930069525379502756875000000000000, 0, 16186254772176136363636363636347450108864187500000000000, 0, 0], ![0, 0, 0, 0, 0, 218531468531468531468531468531250000000000000000000000000, 0, 218531468531468531468531468531250000000000000000000000000, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 437062937062937062937062937062500000000000000000000000000]]
def profileIndex : Fin 6 → Fin 9 → Fin 3 → Fin 12 :=
  ![![![0, 1, 2], ![3, 3, 4], ![3, 5, 3], ![6, 0, 7], ![5, 3, 3], ![8, 9, 0], ![10, 0, 3], ![10, 3, 0], ![11, 0, 0]], ![![1, 0, 2], ![3, 3, 4], ![5, 3, 3], ![0, 6, 7], ![3, 5, 3], ![9, 8, 0], ![0, 10, 3], ![3, 10, 0], ![0, 11, 0]], ![![8, 9, 0], ![3, 5, 3], ![5, 3, 3], ![0, 1, 2], ![3, 3, 4], ![6, 0, 7], ![0, 3, 10], ![3, 0, 10], ![0, 0, 11]], ![![9, 8, 0], ![5, 3, 3], ![3, 5, 3], ![1, 0, 2], ![3, 3, 4], ![0, 6, 7], ![3, 0, 10], ![0, 3, 10], ![0, 0, 11]], ![![6, 0, 7], ![5, 3, 3], ![3, 3, 4], ![8, 9, 0], ![3, 5, 3], ![0, 1, 2], ![3, 10, 0], ![0, 10, 3], ![0, 11, 0]], ![![0, 6, 7], ![3, 5, 3], ![3, 3, 4], ![9, 8, 0], ![5, 3, 3], ![1, 0, 2], ![10, 3, 0], ![10, 0, 3], ![11, 0, 0]]]

def fineCount (r : Fin 6) (j : Fin 9) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 6) (j : Fin 9) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 6) : Fin 9 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent422.regionalWeight (region r)
def n (r : Fin 6) : ℕ := weightCount r * 1000000000000000 * denominator
noncomputable def m (r : Fin 6) (c : RecursiveThinSplit.Split 4 (parent r)) : ℕ :=
  weightCount r * alphaCount (region r) ((splitEquiv r).symm c) * denominator
noncomputable def mu (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  let j := (splitEquiv c.1).symm c.2
  weightCount c.1 * (alphaCount (region c.1) j + alphaCount (region c.1) (Fin.rev j)) *
    fineCount c.1 j i (wordEquiv.symm w)
def totalCount : ℕ := 2000000000000000000000000000000 * denominator

/-- Normalized formulas used to certify the entropy of the same integer data. -/
def weight (r : Fin 6) : ℚ := (weightCount r : ℚ) / 2000000000000000
def alpha (r : Fin 6) (j : Fin 9) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 6) (j : Fin 9) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 6) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 9, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 6) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 9, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 6) (j : Fin 9) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 6) (s : Fin 14) (w : Fin 9) : ℚ :=
  ∑ j : Fin 9,
    if (if boundary i r j then j.val else 9 + (shape r j (yzMode i)).val) = s.val
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
/-- Public recursive entropy witness of each of the three regional parents. -/
def witnessIndex : Fin 3 → Fin 63 := ![48, 49, 50]

/-- Witness maximum-entropy bound minus the split entropy, weighted over the six regions (nats). -/
noncomputable def penaltyRate : ℝ :=
  ∑ r, (weight r : ℝ) * (((DWZFourthRecursiveWitness.witness (witnessIndex (region r))).entropyUpper : ℝ) -
    ratEntropy (alpha r))

noncomputable def explicitRate : ℝ :=
  min (coarseRate - penaltyRate)
    (min (parentRate 1 - compatibilityRate 0) (parentRate 2 - compatibilityRate 1))

end MME.DWZ422Fine


