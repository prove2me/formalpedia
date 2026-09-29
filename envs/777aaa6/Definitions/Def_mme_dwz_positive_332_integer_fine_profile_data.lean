-- Prove2me | Definitions.Def_mme_dwz_positive_332_integer_fine_profile_data
-- name    : mme_dwz_positive_332_integer_fine_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T17:22:51.680893+00:00
-- url     : https://prove2.me/theorems/d347cb43-7f25-48ea-a181-67098173cad3
-- title:
--   Concrete six-region integer fine profiles for the DWZ (3,3,2) component
-- statement:
--   This is a concrete integer fine-profile datum for the original-profile $(3,3,2)$ component at $q=5$. It uses the published object-166 regional weights and regional coarse distributions, in three cyclic orientations paired with their X/Y swaps. Each of the six regions has 10 admissible coarse cells and nine actual two-letter fine words; each physical cell carries the fine profile of the child of its own physical shape (canonical coupled profiles for the (1,1,2) family, exact half-half profiles for the (0,1,3) family). The joint integer counts, the retained-mode marginals, and the explicit rate formula `explicitRate` are defined here. For this non-thin component the coarse branch of `explicitRate` also subtracts `penaltyRate`: the weighted gap between the public recursive maximum-entropy upper bounds of the regional parents (`witnessIndex` into `mme_dwz_fourth_rational_recursive_entropy_data`) and the entropies of the actual split distributions.
-- source:
--   Released q=5 fourth-power certificate (object 166), with the canonical coupled child profiles of mme_dwz_fourth_coupled63_canonical_row_data and exact half-half elementary child profiles.

import Definitions.Def_mme_dwz_positive_332_regional_profile_data
import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib

open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace MME.DWZ332Fine

def region : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def keptMode : Fin 6 → Fin 3 := ![2,2,1,0,0,1]
def parent : Fin 6 → Fin 3 → ℕ := ![![3, 3, 2], ![3, 3, 2], ![3, 2, 3], ![2, 3, 3], ![2, 3, 3], ![3, 2, 3]]
def shape : Fin 6 → Fin 10 → Fin 3 → Fin 5 := ![![![0, 2, 2], ![0, 3, 1], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0]], ![![2, 0, 2], ![3, 0, 1], ![1, 1, 2], ![2, 1, 1], ![3, 1, 0], ![0, 2, 2], ![1, 2, 1], ![2, 2, 0], ![0, 3, 1], ![1, 3, 0]], ![![2, 2, 0], ![3, 1, 0], ![1, 2, 1], ![2, 1, 1], ![3, 0, 1], ![0, 2, 2], ![1, 1, 2], ![2, 0, 2], ![0, 1, 3], ![1, 0, 3]], ![![2, 2, 0], ![1, 3, 0], ![2, 1, 1], ![1, 2, 1], ![0, 3, 1], ![2, 0, 2], ![1, 1, 2], ![0, 2, 2], ![1, 0, 3], ![0, 1, 3]], ![![2, 0, 2], ![1, 0, 3], ![2, 1, 1], ![1, 1, 2], ![0, 1, 3], ![2, 2, 0], ![1, 2, 1], ![0, 2, 2], ![1, 3, 0], ![0, 3, 1]], ![![0, 2, 2], ![0, 1, 3], ![1, 2, 1], ![1, 1, 2], ![1, 0, 3], ![2, 2, 0], ![2, 1, 1], ![2, 0, 2], ![3, 1, 0], ![3, 0, 1]]]
def alphaCount : Fin 3 → Fin 10 → ℕ := ![![11575956688666, 1723405058976, 157279157060661, 317820064461703, 11601366036420, 11601362086111, 317819998083580, 157279324153744, 1723405454613, 11575960915526], ![11681507582032, 1688281258421, 159405497875783, 315602239550058, 11622375802350, 11622357309292, 315602376113826, 159405556021198, 1688280741821, 11681527745219], ![94130805287995, 83410709655232, 111862779944041, 116329880249903, 94265817837461, 94001902796808, 116593786312111, 111862794010101, 83674615716095, 93866908190253]]
def denominator : ℕ := 2000000000000002000000000000000000000000000000
def profileCount : Fin 11 → Fin 9 → ℕ :=
  ![![2000000000000002000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 114150878940904114150878940904000000000000000, 0, 1771698305317901771698305317900000000000000000, 0, 114150815741196114150815741196000000000000000, 0, 0], ![0, 0, 114150815741196114150815741196000000000000000, 0, 1771698305317901771698305317900000000000000000, 0, 114150878940904114150878940904000000000000000, 0, 0], ![0, 0, 0, 0, 0, 1000000000000001000000000000000000000000000000, 0, 1000000000000001000000000000000000000000000000, 0], ![0, 1000000000000001000000000000000000000000000000, 0, 1000000000000001000000000000000000000000000000, 0, 0, 0, 0, 0], ![0, 0, 11981381144089027743152956589725126658426929, 0, 1976037237711823944513694086820549746683146142, 0, 11981381144089027743152956589725126658426929, 0, 0], ![0, 0, 42000000000000042000000000000000000000000000, 0, 1916000000000001916000000000000000000000000000, 0, 42000000000000042000000000000000000000000000, 0, 0], ![0, 0, 105797950641722105797950641722000000000000000, 0, 1788403940015427788403940015426000000000000000, 0, 105798109342852105798109342852000000000000000, 0, 0], ![0, 0, 105798109342852105798109342852000000000000000, 0, 1788403940015427788403940015426000000000000000, 0, 105797950641722105797950641722000000000000000, 0, 0], ![0, 0, 74068301837478074068301837478000000000000000, 0, 1851863395384541851863395384540000000000000000, 0, 74068302777982074068302777982000000000000000, 0, 0], ![0, 0, 74068302777982074068302777982000000000000000, 0, 1851863395384541851863395384540000000000000000, 0, 74068301837478074068301837478000000000000000, 0, 0]]
def profileIndex : Fin 6 → Fin 10 → Fin 3 → Fin 11 :=
  ![![![0, 1, 2], ![0, 3, 4], ![4, 4, 5], ![4, 6, 4], ![4, 3, 0], ![7, 0, 8], ![6, 4, 4], ![9, 10, 0], ![3, 0, 4], ![3, 4, 0]], ![![1, 0, 2], ![3, 0, 4], ![4, 4, 5], ![6, 4, 4], ![3, 4, 0], ![0, 7, 8], ![4, 6, 4], ![10, 9, 0], ![0, 3, 4], ![4, 3, 0]], ![![9, 10, 0], ![3, 4, 0], ![4, 6, 4], ![6, 4, 4], ![3, 0, 4], ![0, 1, 2], ![4, 4, 5], ![7, 0, 8], ![0, 4, 3], ![4, 0, 3]], ![![10, 9, 0], ![4, 3, 0], ![6, 4, 4], ![4, 6, 4], ![0, 3, 4], ![1, 0, 2], ![4, 4, 5], ![0, 7, 8], ![4, 0, 3], ![0, 4, 3]], ![![7, 0, 8], ![4, 0, 3], ![6, 4, 4], ![4, 4, 5], ![0, 4, 3], ![9, 10, 0], ![4, 6, 4], ![0, 1, 2], ![4, 3, 0], ![0, 3, 4]], ![![0, 7, 8], ![0, 4, 3], ![4, 6, 4], ![4, 4, 5], ![4, 0, 3], ![10, 9, 0], ![6, 4, 4], ![1, 0, 2], ![3, 4, 0], ![3, 0, 4]]]

def fineCount (r : Fin 6) (j : Fin 10) (i : Fin 3) (w : Fin 9) : ℕ :=
  profileCount (profileIndex r j i) w

def word : Fin 9 → CompleteSplit.CompleteWord 2 :=
  ![![0,0],![0,1],![0,2],![1,0],![1,1],![1,2],![2,0],![2,1],![2,2]]

/-- The nine actual two-letter words, in lexicographic order. -/
noncomputable def wordEquiv : Fin 9 ≃ CompleteSplit.CompleteWord 2 :=
  Equiv.ofBijective word (by decide +kernel)

/-- The eight admissible left-half grades in each physical orientation. -/
def splitMap (r : Fin 6) (j : Fin 10) : RecursiveThinSplit.Split 4 (parent r) :=
  ⟨shape r j, by
    have h : ∀ r j,
      (shape r j 0).val + (shape r j 1).val + (shape r j 2).val = 4 ∧
        ∀ i, (shape r j i).val ≤ parent r i := by decide +kernel
    exact h r j⟩

noncomputable def splitEquiv (r : Fin 6) : Fin 10 ≃ RecursiveThinSplit.Split 4 (parent r) :=
  Equiv.ofBijective (splitMap r) (by
    have h : ∀ r, Function.Bijective (splitMap r) := by decide +kernel
    exact h r)

theorem parent_total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * 4 := by decide +kernel

def weightCount (r : Fin 6) : ℕ := DWZPositiveComponent332.regionalWeight (region r)
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
def alpha (r : Fin 6) (j : Fin 10) : ℚ := (alphaCount (region r) j : ℚ) / 1000000000000000
def beta (r : Fin 6) (j : Fin 10) (i : Fin 3) (w : Fin 9) : ℚ :=
  (fineCount r j i w : ℚ) / denominator

def coarse (r : Fin 6) (i : Fin 3) (g : Fin 5) : ℚ :=
  ∑ j : Fin 10, if shape r j i = g then alpha r j else 0

def jointWord (r : Fin 6) (i : Fin 3) (a b : Fin 9) : ℚ :=
  ∑ j : Fin 10, alpha r j * beta r j i a * beta r (Fin.rev j) i b

def boundary (i : Fin 2) (r : Fin 6) (j : Fin 10) : Bool :=
  if i = 0 then shape r j 2 = 0 else shape r j 0 = 0 ∨ shape r j 1 = 0

/-- Individual boundary parts 0..7 and grouped interior parts 8..12. -/
def partMass (i : Fin 2) (r : Fin 6) (s : Fin 15) (w : Fin 9) : ℚ :=
  ∑ j : Fin 10,
    if (if boundary i r j then j.val else 10 + (shape r j (yzMode i)).val) = s.val
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
def witnessIndex : Fin 3 → Fin 63 := ![39, 40, 41]

/-- Witness maximum-entropy bound minus the split entropy, weighted over the six regions (nats). -/
noncomputable def penaltyRate : ℝ :=
  ∑ r, (weight r : ℝ) * (((DWZFourthRecursiveWitness.witness (witnessIndex (region r))).entropyUpper : ℝ) -
    ratEntropy (alpha r))

noncomputable def explicitRate : ℝ :=
  min (coarseRate - penaltyRate)
    (min (parentRate 1 - compatibilityRate 0) (parentRate 2 - compatibilityRate 1))

end MME.DWZ332Fine


