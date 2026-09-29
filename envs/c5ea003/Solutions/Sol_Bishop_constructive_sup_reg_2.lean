-- Prove2me | solution 2 for Bishop.constructive_sup_reg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:47:48.512252+00:00
-- url     : https://prove2.me/submissions/1566e42a-1653-4b9c-868a-672e58277bc3

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveSup

open Bishop Set Filter Topology in
theorem solution {S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) :
    ∃ x : Reg, IsLUB S x.toReal ∧
      ∀ k : ℕ, ∃ n : ℕ, x.approx k = (bisect D.L a₀ b₀ n).1 := by
  -- the trisection enclosures converge to the supremum
  have hsup : ∃ u : ℝ, IsLUB S u ∧ ∀ n : ℕ,
      ((bisect D.L a₀ b₀ n).1 : ℝ) ≤ u ∧ u ≤ ((bisect D.L a₀ b₀ n).2 : ℝ) ∧
        ((bisect D.L a₀ b₀ n).2 : ℝ) - ((bisect D.L a₀ b₀ n).1 : ℝ)
          = (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) := by
    -- the search keeps a proper enclosure whose width shrinks by `2/3` per step
    have inv : ∀ n, (bisect D.L a₀ b₀ n).1 < (bisect D.L a₀ b₀ n).2 ∧
        Enclosing S (bisect D.L a₀ b₀ n) ∧
        (bisect D.L a₀ b₀ n).2 - (bisect D.L a₀ b₀ n).1 = (2 / 3 : ℚ) ^ n * (b₀ - a₀) := by
      intro n
      induction n with
      | zero => exact ⟨hab, h₀, by simp [bisect]⟩
      | succ n ih =>
        rw [show bisect D.L a₀ b₀ (n + 1) = bisectStep D.L (bisect D.L a₀ b₀ n) from rfl]
        generalize bisect D.L a₀ b₀ n = pq at ih ⊢
        obtain ⟨p, q⟩ := pq
        obtain ⟨hlt, ⟨hup, s, hs, hps⟩, hw⟩ := ih
        simp only at hlt hup hps hw
        have hm : p + (q - p) / 3 < p + 2 * (q - p) / 3 := by linarith
        cases hL : D.L (p + (q - p) / 3) (p + 2 * (q - p) / 3)
        · have hstep : bisectStep D.L (p, q) = (p + (q - p) / 3, q) := by
            simp only [bisectStep, hL, Bool.false_eq_true, if_false]
          rw [hstep]
          refine ⟨by linarith, ⟨hup, D.witness _ _ hm hL⟩, ?_⟩
          rw [pow_succ]
          linear_combination (2 / 3 : ℚ) * hw
        · have hstep : bisectStep D.L (p, q) = (p, p + 2 * (q - p) / 3) := by
            simp only [bisectStep, hL, if_true]
          rw [hstep]
          refine ⟨by linarith, ⟨D.upper _ _ hm hL, s, hs, hps⟩, ?_⟩
          rw [pow_succ]
          linear_combination (2 / 3 : ℚ) * hw
    obtain ⟨-, ⟨hup0, s0, hs0, -⟩, -⟩ := inv 0
    have hne : S.Nonempty := ⟨s0, hs0⟩
    have hbdd : BddAbove S := ⟨(b₀ : ℝ), fun s hs => hup0 s hs⟩
    refine ⟨sSup S, isLUB_csSup hne hbdd, fun n => ?_⟩
    obtain ⟨-, ⟨hup, s, hs, hps⟩, hw⟩ := inv n
    refine ⟨(hps.trans_le (le_csSup hbdd hs)).le, csSup_le hne hup, ?_⟩
    have hw' := congrArg (fun t : ℚ => (t : ℝ)) hw
    push_cast at hw'
    exact hw'
  obtain ⟨u, hlub, hn⟩ := hsup
  have hw : (0 : ℝ) < (b₀ : ℝ) - (a₀ : ℝ) := by
    have : (a₀ : ℝ) < b₀ := by exact_mod_cast hab
    linarith
  -- a depth `N k` at which the enclosure is narrower than `1/(k+1)`
  have hN : ∀ k : ℕ, ∃ M : ℕ, (2 / 3 : ℝ) ^ M * ((b₀ : ℝ) - (a₀ : ℝ)) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < 1 / ((k : ℝ) + 1) / ((b₀ : ℝ) - (a₀ : ℝ)) by positivity)
      (show (2 / 3 : ℝ) < 1 by norm_num)
    exact ⟨M, ((lt_div_iff₀ hw).1 hM).le⟩
  choose N hNk using hN
  have hclose : ∀ k : ℕ, |((bisect D.L a₀ b₀ (N k)).1 : ℝ) - u| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hn (N k)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith [hNk k]
  let x : Reg := ⟨fun k => (bisect D.L a₀ b₀ (N k)).1, by
    intro m n
    have hreal : |((bisect D.L a₀ b₀ (N m)).1 : ℝ) - ((bisect D.L a₀ b₀ (N n)).1 : ℝ)|
        ≤ 1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
      calc |((bisect D.L a₀ b₀ (N m)).1 : ℝ) - ((bisect D.L a₀ b₀ (N n)).1 : ℝ)|
          ≤ |((bisect D.L a₀ b₀ (N m)).1 : ℝ) - u| + |u - ((bisect D.L a₀ b₀ (N n)).1 : ℝ)| :=
            abs_sub_le _ _ _
        _ ≤ 1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
            rw [abs_sub_comm u]
            exact add_le_add (hclose m) (hclose n)
    beta_reduce
    have h' : ((|(bisect D.L a₀ b₀ (N m)).1 - (bisect D.L a₀ b₀ (N n)).1| : ℚ) : ℝ)
        ≤ ((1 / ((m : ℚ) + 1) + 1 / ((n : ℚ) + 1) : ℚ) : ℝ) := by
      push_cast
      exact hreal
    refine le_trans (Rat.cast_le.1 h') (le_of_eq ?_)
    ring⟩
  refine ⟨x, ?_, fun k => ⟨N k, rfl⟩⟩
  have hlim : x.toReal = u := by
    have h2 : Tendsto (fun k => ((x.approx k : ℚ) : ℝ)) atTop (𝓝 u) := by
      have hl : Tendsto (fun k : ℕ => u - 1 / ((k : ℝ) + 1)) atTop (𝓝 u) := by
        simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hu : Tendsto (fun k : ℕ => u + 1 / ((k : ℝ) + 1)) atTop (𝓝 u) := by
        simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun k => ?_) (fun k => ?_)
      · show u - 1 / ((k : ℝ) + 1) ≤ ((bisect D.L a₀ b₀ (N k)).1 : ℝ)
        linarith [(abs_le.1 (hclose k)).1]
      · show ((bisect D.L a₀ b₀ (N k)).1 : ℝ) ≤ u + 1 / ((k : ℝ) + 1)
        linarith [(abs_le.1 (hclose k)).2]
    exact tendsto_nhds_unique x.tendsto_toReal h2
  rw [hlim]
  exact hlub
