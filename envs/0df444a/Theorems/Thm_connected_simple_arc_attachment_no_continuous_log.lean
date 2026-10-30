-- Prove2me | Theorems.Thm_connected_simple_arc_attachment_no_continuous_log
-- name    : connected_simple_arc_attachment_no_continuous_log
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T03:13:52.322899+00:00
-- url     : https://prove2.me/theorems/192efa39-8303-4dbe-8d90-22363baaf03f
-- title:
--   A simple arc attached to one component creates a logarithm obstruction
-- statement:
--   Let $X$ be Hausdorff, let $K\subset X$ be compact, and let $a:[0,1]\to X$ be continuous and injective. Suppose $a((0,1))$ is disjoint from $K$ and $a(1)$ belongs to the connected component of $K$ containing $a(0)$. Then there is a continuous nowhere-zero complex-valued function on $K\cup a([0,1])$ which has no continuous logarithm on that union.
--
--   This is a logarithm obstruction relevant to planar separation; it does not itself assert separation of a planar complement.
-- source:
--   Elementary winding-map construction related to the continuous exponential-lift obstruction https://prove2.me/theorems/653f90e1-495b-43e7-8909-7910d74b7dd9 . Its application to planar separation uses an additional classical logarithm theorem; see E. M. Chirka, Sbornik: Mathematics, p. 1074, https://www.mathnet.ru/links/df3b73701989c88d18d93346e0ffdc1b/sm8756_eng.pdf .

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Set

theorem connected_simple_arc_attachment_no_continuous_log {X : Type} [TopologicalSpace X] [T2Space X]
    (K : Set X) (a : ℝ → X) (hK : IsCompact K)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hi : InjOn a (Icc (0 : ℝ) 1))
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hsame : a 1 ∈ connectedComponentIn K (a 0)) :
    ∃ F : X → ℂ, ContinuousOn F (K ∪ a '' Icc (0 : ℝ) 1) ∧
      (∀ z ∈ K ∪ a '' Icc (0 : ℝ) 1, F z ≠ 0) ∧
      ¬ ∃ f : X → ℂ, ContinuousOn f (K ∪ a '' Icc (0 : ℝ) 1) ∧
        EqOn (fun x => Complex.exp (f x)) F (K ∪ a '' Icc (0 : ℝ) 1) := by sorry
