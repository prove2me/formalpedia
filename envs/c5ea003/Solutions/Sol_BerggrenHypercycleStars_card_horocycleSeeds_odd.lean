-- Prove2me | solution 1 for BerggrenHypercycleStars.card_horocycleSeeds_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:29:50.286822+00:00
-- url     : https://prove2.me/submissions/2a4b192b-1ea9-451e-9529-2112418e11a0

-- Sol generated from Cryptography/BerggrenStars/HorocycleCensus.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HorocycleCensus
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars

/-!
# The curves of the Berggren picture: horocycle census

Besides the *stars* of hypercycles studied in `Cryptography.BerggrenStars.HypercycleStars`,
a picture of the Berggren tree embedded in the Poincaré half-plane by `z(m,n) = (n+i)/m` shows a
second family of curves: the **horizontal lines**, which are the horocycles based at the boundary
point `∞`. The nodes at height `1/m` are exactly the Euclid seeds with first coordinate `m`.

## Main results

* `card_horocycleSeeds_even`, `card_horocycleSeeds_odd` : an exact census of each horocycle.
  The horocycle at height `1/m` carries exactly `φ(m)` nodes when `m` is even, and exactly
  `φ(m)/2` nodes when `m` is odd — Euler's totient is the *occupation number* of the horocycle.
* `horocycleSeeds_nonempty` : every horocycle at height `1/m` with `m ≥ 2` is occupied.
* `horocycle_pairwise_separated` : the nodes on one horocycle are uniformly separated, at
  pairwise hyperbolic distance at least `arcosh (3/2)`, however deep in the tree they lie. So
  the horizontal curves of the picture are *uniformly discrete* point sets, in sharp contrast
  with the hypercycle rays, along which the nodes accumulate (`step_along_spoke_tendsto_zero`).
-/

open BerggrenHypercycleStars

open Real UpperHalfPlane








open BerggrenHypercycleStars in
theorem solution(m : ℕ) (hm : m % 2 = 1) (hm3 : 3 ≤ m) :
    2 * (horocycleSeeds m).card = Nat.totient m := by
  classical
  have hTcard : ((Finset.range m).filter m.Coprime).card = Nat.totient m :=
    (Nat.totient_eq_card_coprime m).symm
  -- the even totatives are exactly the seeds on this horocycle
  have hE : horocycleSeeds m
      = ((Finset.range m).filter m.Coprime).filter (fun n => n % 2 = 0) := by
    rw [horocycleSeeds, Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro n _
    constructor
    · rintro ⟨hcop, hpar⟩; exact ⟨hcop, by omega⟩
    · rintro ⟨hcop, hpar⟩; exact ⟨hcop, by omega⟩
  -- the odd totatives are the image of the even ones under `n ↦ m - n`
  have hbij : (((Finset.range m).filter m.Coprime).filter (fun n => n % 2 = 0)).card
      = (((Finset.range m).filter m.Coprime).filter (fun n => ¬ n % 2 = 0)).card := by
    refine Finset.card_bij' (fun n _ => m - n) (fun n _ => m - n) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
      obtain ⟨⟨hlt, hcop⟩, hpar⟩ := ha
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
        omega
      exact ⟨⟨by omega, (Nat.coprime_self_sub_right hlt.le).2 hcop⟩, by omega⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
      obtain ⟨⟨hlt, hcop⟩, hpar⟩ := ha
      exact ⟨⟨by omega, (Nat.coprime_self_sub_right hlt.le).2 hcop⟩, by omega⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      show m - (m - a) = a
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      show m - (m - a) = a
      omega
  have hsplit :
      (((Finset.range m).filter m.Coprime).filter (fun n => n % 2 = 0)).card
        + (((Finset.range m).filter m.Coprime).filter (fun n => ¬ n % 2 = 0)).card
      = ((Finset.range m).filter m.Coprime).card :=
    Finset.card_filter_add_card_filter_not _
  rw [hE, ← hTcard, ← hsplit, ← hbij]
  ring
