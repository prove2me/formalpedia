-- Prove2me | solution 1 for every_stabilizing_observable_has_fixed_universality_class
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:50:39.293871+00:00
-- url     : https://prove2.me/submissions/5dcddb24-2676-4136-bd83-e224e840fb62

import Mathlib
import Definitions.Def_Bridges_RenormalizationUniversality
universe u
theorem solution {α : Type u} [ClosureFlow α] {x : α} (hw : StabilizationWitness x) :
    ∃ y, IsRGFixed y ∧ AsymptoticCong x y := by
  obtain ⟨N, hN⟩ := hw
  -- the orbit point at the stabilisation time is a fixed point
  have hfix : IsRGFixed (rgIterate N x) := hN N le_rfl
  have hiter : ∀ k, rgIterate k (rgIterate N x) = rgIterate N x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show ClosureFlow.step (rgIterate k (rgIterate N x)) = rgIterate N x
      rw [ih]
      exact hfix
  -- and the orbit of `x` sits there from time `N` on
  have hstab : ∀ n, N ≤ n → rgIterate n x = rgIterate N x := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [hN n hn, ih]
  exact ⟨rgIterate N x, hfix, N, fun n hn => by rw [hiter, hstab n hn]⟩
