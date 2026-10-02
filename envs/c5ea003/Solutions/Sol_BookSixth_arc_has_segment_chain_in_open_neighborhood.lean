-- Prove2me | solution 1 for BookSixth.arc_has_segment_chain_in_open_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T08:19:51.199427+00:00
-- url     : https://prove2.me/submissions/917e7fe2-842f-4b2a-9e34-bec29e57f035

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open scoped Topology
open Set Filter
open BookSixth

private theorem segment_chain_in_open_neighborhood
    {U K : Set (Fin 2 → ℝ)} (hU : IsOpen U)
    (hK : IsPreconnected K) (hKU : K ⊆ U)
    {x y : Fin 2 → ℝ} (hx : x ∈ K) (hy : y ∈ K) :
    Relation.ReflTransGen (fun a b => segment ℝ a b ⊆ U) x y := by
  let P := Relation.ReflTransGen (fun a b : Fin 2 → ℝ => segment ℝ a b ⊆ U)
  apply hK.induction₂ P ?_ ?_ ?_ hx hy
  · intro a ha
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU a (hKU ha)
    have hnear : ∀ᶠ b in 𝓝 a, P a b := by
      filter_upwards [Metric.ball_mem_nhds a hr] with b hb
      apply Relation.ReflTransGen.single
      exact ((convex_ball a r).segment_subset
        (Metric.mem_ball_self hr) hb).trans hball
    exact hnear.filter_mono nhdsWithin_le_nhds
  · intro a b c _ _ _ hab hbc
    exact hab.trans hbc
  · intro a b _ _ hab
    apply Relation.ReflTransGen.symmetric
      (r := fun a b : Fin 2 → ℝ => segment ℝ a b ⊆ U) ?_ hab
    intro c d hcd
    simpa only [segment_symm ℝ d c] using hcd

theorem solution {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M)
    {U : Set (Fin 2 → ℝ)} (hU : IsOpen U)
    (himage : Set.range (D.arc e) ⊆ U) :
    Relation.ReflTransGen (fun a b => segment ℝ a b ⊆ U)
      (D.vertex (D.left e)) (D.vertex (D.right e)) := by
  have h :
      Relation.ReflTransGen (fun a b => segment ℝ a b ⊆ U)
        (D.arc e ⟨0, by constructor <;> norm_num⟩)
        (D.arc e ⟨1, by constructor <;> norm_num⟩) := by
    apply segment_chain_in_open_neighborhood hU
      (isPreconnected_range (D.continuous_arc e)) himage
    · exact Set.mem_range_self _
    · exact Set.mem_range_self _
  simpa only [D.start, D.finish] using h
