-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.tailsup_summable
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:49:22.15004+00:00
-- url     : https://prove2.me/submissions/7c3fc209-f3e8-4591-aa38-a201013d9fef

import Mathlib

namespace AnalyticCombinatorics end AnalyticCombinatorics
namespace AnalyticCombinatorics.Ch8 end AnalyticCombinatorics.Ch8
namespace AnalyticCombinatorics.Ch8.Partitions end AnalyticCombinatorics.Ch8.Partitions
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos end AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: summability from a `B`-step geometric contraction

If `f ≥ 0` and `f(n+B) ≤ q·f(n)` with `0 ≤ q < 1`, then `f` is summable.  Clean proof via uniformly
bounded partial sums: splitting `∑_{range m} f` at `B` and applying the step bound gives
`S_m ≤ S_B + q·S_m`, hence `S_m ≤ S_B/(1−q)`.  No floor/rpow needed.  This converts the tail-sup
block-oscillation contraction `V(R) ≤ (1−δ)·V(R−B)` into `Summable V` for the §9 convergence engine.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma summable_of_step_le {f : ℕ → ℝ} {q : ℝ} {B : ℕ}
    (hf : ∀ n, 0 ≤ f n) (hq1 : q < 1) (hq0 : 0 ≤ q)
    (hstep : ∀ n, f (n + B) ≤ q * f n) :
    Summable f := by
  have hmono : Monotone (fun m => ∑ i ∈ Finset.range m, f i) := by
    intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hab))
      (fun i _ _ => hf i)
  have hkey : ∀ m, (∑ i ∈ Finset.range m, f i)
      ≤ (∑ i ∈ Finset.range B, f i) + q * ∑ i ∈ Finset.range m, f i := by
    intro m
    rcases le_or_gt m B with hmB | hmB
    · have h1 : (∑ i ∈ Finset.range m, f i) ≤ ∑ i ∈ Finset.range B, f i := hmono hmB
      have h2 : 0 ≤ q * ∑ i ∈ Finset.range m, f i :=
        mul_nonneg hq0 (Finset.sum_nonneg (fun i _ => hf i))
      linarith
    · obtain ⟨d, rfl⟩ : ∃ d, m = B + d := ⟨m - B, by omega⟩
      have hadd : (∑ i ∈ Finset.range (B + d), f i)
          = (∑ i ∈ Finset.range B, f i) + ∑ i ∈ Finset.range d, f (B + i) :=
        Finset.sum_range_add f B d
      have hstep_sum : ∑ i ∈ Finset.range d, f (B + i) ≤ q * ∑ i ∈ Finset.range d, f i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => by rw [add_comm B i]; exact hstep i)
      have hdle : (∑ i ∈ Finset.range d, f i) ≤ ∑ i ∈ Finset.range (B + d), f i :=
        hmono (by omega)
      rw [hadd] at hdle ⊢
      nlinarith [hstep_sum, hdle, hq0, mul_nonneg hq0 (sub_nonneg.mpr hdle)]
  apply summable_of_sum_range_le (c := (∑ i ∈ Finset.range B, f i) / (1 - q)) hf
  intro n
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - q)]
  nlinarith [hkey n]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# R7 Fact B via Doeblin: the tail-sup of block oscillation is summable

The §9 connection's key device: if block oscillation `W ≥ 0` is bounded and satisfies the slab
contraction `W R ≤ q · sSup(W '' {s ≥ R−B})` (`0 ≤ q < 1`), then its tail-sup
`V R := sSup(W '' {s ≥ R})` is monotone-dominated, so `V R ≤ q · V(R−B)`, hence `Summable V`.  This
turns the local (comparable-rank) contraction into a global summable bound, resolving the far-pair
obstruction.  `csSup`-based.  Opus-authored.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos in
theorem solution {W : ℕ → ℝ} {q M : ℝ} {B : ℕ}
    (hWnn : ∀ R, 0 ≤ W R) (hWbd : ∀ R, W R ≤ M)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ R, W R ≤ q * sSup (W '' {s | R - B ≤ s})) :
    Summable (fun R => sSup (W '' {s | R ≤ s})) := by
  set V := fun R => sSup (W '' {s | R ≤ s}) with hV
  have hbdd : ∀ R, BddAbove (W '' {s | R ≤ s}) := by
    intro R; exact ⟨M, by rintro _ ⟨s, _, rfl⟩; exact hWbd s⟩
  have hbdd' : ∀ R, BddAbove (W '' {s | R - B ≤ s}) := by
    intro R; exact ⟨M, by rintro _ ⟨s, _, rfl⟩; exact hWbd s⟩
  have hmem : ∀ R, W R ∈ W '' {s | R ≤ s} := fun R => ⟨R, le_refl R, rfl⟩
  have hWleV : ∀ R, W R ≤ V R := fun R => le_csSup (hbdd R) (hmem R)
  have hVnn : ∀ R, 0 ≤ V R := fun R => (hWnn R).trans (hWleV R)
  -- antitone: smaller index ⟹ larger sup
  have hVanti : ∀ {a b : ℕ}, a ≤ b → V b ≤ V a := by
    intro a b hab
    refine csSup_le_csSup (hbdd a) ⟨W b, hmem b⟩ ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, le_trans hab hs, rfl⟩
  -- the contraction on V
  have hVcontract : ∀ R, V R ≤ q * V (R - B) := by
    intro R
    refine csSup_le ⟨W R, hmem R⟩ ?_
    rintro _ ⟨s, (hs : R ≤ s), rfl⟩
    calc W s ≤ q * sSup (W '' {s' | s - B ≤ s'}) := hcontract s
      _ ≤ q * V (R - B) := by
          apply mul_le_mul_of_nonneg_left _ hq0
          exact hVanti (by omega)
  -- summability via the B-step contraction V(n+B) ≤ q V(n)
  apply summable_of_step_le hVnn hq1 hq0
  intro n
  have := hVcontract (n + B)
  simpa using this
