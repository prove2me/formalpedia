-- Prove2me | solution 1 for TropicalRR.const_of_lap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:54:20.874487+00:00
-- url     : https://prove2.me/submissions/5eb79768-9ff5-40ca-99a4-b8f458944142

import Mathlib
import Definitions.Def_Combinatorics_Basic
open TropicalRR in
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {f : V → ℤ} (h : lap G f = 0) (u v : V) : f u = f v := by
  classical
  -- maximum principle: take a vertex where `f` is largest
  obtain ⟨v0, -, hv0⟩ := Finset.exists_max_image Finset.univ f ⟨u, Finset.mem_univ u⟩
  have hle : ∀ x, f x ≤ f v0 := fun x => hv0 x (Finset.mem_univ x)
  -- at a maximum, `Δf = Σ (f x - f w) = 0` with nonnegative terms forces every neighbour to be maximal
  have hstep : ∀ x y, f x = f v0 → G.Adj x y → f y = f v0 := by
    intro x y hx hxy
    have hl : ∑ w ∈ G.neighborFinset x, (f x - f w) = 0 := congrFun h x
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => by have := hle w; omega)).mp hl y
      ((G.mem_neighborFinset x y).mpr hxy)
    omega
  -- propagate along walks; the graph is connected
  have hwalk : ∀ x y (p : G.Walk x y), f x = f v0 → f y = f v0 := by
    intro x y p
    induction p with
    | nil => exact id
    | cons hadj p ih => exact fun hx => ih (hstep _ _ hx hadj)
  have hall : ∀ x, f x = f v0 := fun x => hwalk v0 x (hc.preconnected v0 x).some rfl
  rw [hall u, hall v]
