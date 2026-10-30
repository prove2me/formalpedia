-- Prove2me | Theorems.Thm_planar_crosscut_complement_nonempty_disconnected__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a2
-- name    : planar_crosscut_complement_nonempty_disconnected__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:48.851454+00:00
-- url     : https://prove2.me/theorems/42b4f0b5-a0b7-426f-a906-fd3edf8d84ac
-- title:
--   A planar crosscut leaves a nonempty disconnected complement
-- statement:
--   Removing this injective crosscut from the connected open planar set leaves a nonempty disconnected set. This is the substantive planar separation step. A proof route is the classical crosscut separation theorem; injectivity on the closed interval ensures the arc has distinct endpoints. The cited URL inspected here does not supply that theorem, so its precise source hypotheses still need confirmation.
-- source:
--   M. H. A. Newman, Elements of the Topology of Plane Sets of Points, Theorem V.11.7; see its statement at https://iiscoe.wordpress.com/wp-content/uploads/2020/07/as_triangulation_details-2.pdf . Supporting the same-component branch https://prove2.me/theorems/c8030f71-3663-4ed8-be54-5fe08a9e8720 .

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousOn

open Set

theorem planar_crosscut_complement_nonempty_disconnected__p2m_bfad0b38_624c_4f44_b180_c550615568f1_a2
    (U : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1)) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hinside : a '' Ioo (0 : ℝ) 1 ⊆ U)
    (hzero : a 0 ∈ frontier U) (hone : a 1 ∈ frontier U)
    (hsame : a 1 ∈ connectedComponentIn (frontier U) (a 0)) :
    (((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ)).Nonempty ∧
      ¬ IsConnected (U \ (a '' Icc (0 : ℝ) 1))) := by sorry
