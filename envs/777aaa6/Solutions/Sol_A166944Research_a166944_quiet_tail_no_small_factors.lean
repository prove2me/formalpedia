-- Prove2me | solution 1 for A166944Research.a166944_quiet_tail_no_small_factors
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-20T00:24:31.28918+00:00
-- url     : https://prove2.me/submissions/1754b452-bf7f-4b76-beb1-3978a2f4bdfe

import Definitions.Def_a166944_moving_horizon
import Definitions.Def_a166944_factor_layer

open A166944Research

/-- On a quiet interval, the offset stays constant. Evaluating the recurrence
therefore gives the two gcds used in the reflection argument. -/
private theorem quiet_gcd {sf Cf : Nat} (hstate : IsMovingHorizonState sf Cf)
    (hquiet : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1)
    (j : Nat) (hsj : sf < j) (hjC : j ≤ Cf) :
    (j % 2 = 0 → Nat.gcd j (Cf - 1) = 1) ∧
    (j % 2 = 1 → Nat.gcd (j - 2) (Cf + 1) = 1) := by
  rcases hstate with ⟨hs, hD, hsc⟩
  unfold D at hD
  have htail (t : Nat) (ht : sf + t ≤ Cf) : a (sf + t) = Cf + (sf + t) := by
    induction t with
    | zero => simp only [Nat.add_zero]; omega
    | succ t ih =>
        have hprev := ih (by omega)
        have hunit := hquiet (sf + t + 1) (by omega) (by omega)
        simp only [d, Nat.add_one_sub_one] at hunit
        change a (sf + t + 1) = Cf + (sf + t + 1)
        omega
  have hp := htail (j - 1 - sf) (by omega)
  have hidx : sf + (j - 1 - sf) = j - 1 := by omega
  rw [hidx] at hp
  have hg (k : Nat) : d (k + 2) = if (k + 2) % 2 = 0 then
      Nat.gcd (k + 2) (a (k + 1)) else Nat.gcd k (a (k + 1)) := by
    simp only [d, a]
    split <;> simp_all
  obtain ⟨k, hk⟩ := Nat.le.dest (show 2 ≤ j by omega)
  have hmap : d j = if j % 2 = 0 then Nat.gcd j (a (j - 1))
      else Nat.gcd (j - 2) (a (j - 1)) := by
    subst j
    simpa [Nat.add_comm] using hg k
  rw [hquiet j hsj hjC, hp] at hmap
  constructor
  · intro h
    rw [if_pos h, show Cf + (j - 1) = (Cf - 1) + j by omega] at hmap
    simpa using hmap.symm
  · intro h
    rw [if_neg (by omega : ¬j % 2 = 0), show Cf + (j - 1) = (Cf + 1) + (j - 2) by omega] at hmap
    simpa using hmap.symm

/-- Reflect any putative small divisor back to an index in the quiet tail. -/
theorem solution {sf Cf root : Nat}
    (hstate : IsMovingHorizonState sf Cf)
    (hquiet : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1)
    (hlong : 2 * root < Cf - sf) :
    NoSmallFactor (Cf - 1) root ∧ NoSmallFactor (Cf + 1) root := by
  have hs := hstate.1
  have hsc := hstate.2.2
  by_cases hshort : root < 2
  · constructor <;> intro f hf <;> have := f.isLt <;> omega
  have hgcd := quiet_gcd hstate hquiet
  -- If Cf were odd, the even index Cf - 1 would have gcd(Cf - 1,Cf - 1) = 1.
  have hCe : Cf % 2 = 0 := by
    by_contra h
    have he := (hgcd (Cf - 1) (by omega) (by omega)).1 (by omega)
    rw [Nat.gcd_self] at he
    omega
  constructor
  · intro f hf hdiv
    have hfle := f.isLt
    have hfodd : f.val % 2 = 1 := by
      by_cases h : f.val % 2 = 0
      · have h2 : 2 ∣ f.val := Nat.dvd_of_mod_eq_zero h
        have := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2 hdiv)
        omega
      · omega
    let j := Cf - 1 - f.val
    have hsj : sf < j := by omega
    have hjC : j ≤ Cf := by omega
    have hpar : j % 2 = 0 := by omega
    have hjdiv : f.val ∣ j := Nat.dvd_sub hdiv (Nat.dvd_refl _)
    have hcontra := Nat.dvd_gcd hjdiv hdiv
    rw [(hgcd j hsj hjC).1 hpar] at hcontra
    have := Nat.eq_one_of_dvd_one hcontra
    omega
  · intro f hf hdiv
    have hfle := f.isLt
    let j := Cf + 3 - 2 * f.val
    have hsj : sf < j := by omega
    have hjC : j ≤ Cf := by omega
    have hpar : j % 2 = 1 := by omega
    have hsub : j - 2 = Cf + 1 - 2 * f.val := by omega
    have hjdiv : f.val ∣ j - 2 := by
      rw [hsub]
      exact Nat.dvd_sub hdiv (Nat.dvd_mul_left_of_dvd (Nat.dvd_refl f.val) 2)
    have hcontra := Nat.dvd_gcd hjdiv hdiv
    rw [(hgcd j hsj hjC).2 hpar] at hcontra
    have := Nat.eq_one_of_dvd_one hcontra
    omega
