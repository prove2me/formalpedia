-- Prove2me | solution 1 for CertifiedAdversarialRobustness.margin_lipschitz_implies_linf_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:38:36.986586+00:00
-- url     : https://prove2.me/submissions/dd04fe1d-823e-46cd-83ec-1521088066d4

-- Sol generated from MachineLearning/CertifiedRobustness.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedRobustness

/-!
# Certified robustness and a finite cellular sheaf counterexample

This file isolates a precise contrarian test of the proposed principle.  The
cohomology model is the degree-one cellular cohomology of the constant real
sheaf on the graph consisting of two weight charts and their overlap.  Its
first cohomology vanishes, but this topological fact alone does not constrain
a classifier's decision margin.  A threshold classifier supplies a certified
counterexample.  We also prove a corrected analytic theorem: a positive margin
together with a local Lipschitz estimate gives an explicit `L∞` certificate.
-/

open CertifiedAdversarialRobustness






/-! ## A two-chart cellular sheaf

A section over the two vertices is a pair `(a,b)`.  Its Čech/cellular
coboundary on their oriented overlap is `b-a`.  Degree-one cohomology vanishes
when every overlap cochain is such a coboundary.
-/








/-! ## Corrected positive statement

Topology can organize local data, but a numerical certificate requires an
analytic bridge.  The next result gives that bridge without assuming any
cohomology: positive score margin and a local Lipschitz bound imply robustness.
-/



open CertifiedAdversarialRobustness in
theorem solution{n : ℕ}
    (score : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (margin L radius : ℝ)
    (hmargin : margin ≤ score x) (hmargin_pos : 0 < margin)
    (hbudget : L * radius < margin)
    (hlip : ∀ y, linfDist x y < radius →
      |score y - score x| ≤ L * linfDist x y)
    (hL : 0 ≤ L) :
    CertifiedAt linfDist score x radius := by
  intro y hy
  have hdist : L * linfDist x y < margin := by
    calc
      L * linfDist x y ≤ L * radius :=
        mul_le_mul_of_nonneg_left (le_of_lt hy) hL
      _ < margin := hbudget
  have habs := hlip y hy
  have hlower : score x - score y ≤ L * linfDist x y := by
    calc
      score x - score y ≤ |score y - score x| := by
        rw [abs_sub_comm]
        exact le_abs_self (score x - score y)
      _ ≤ L * linfDist x y := habs
  have hypos : 0 < score y := by linarith
  have hxpos : 0 < score x := lt_of_lt_of_le hmargin_pos hmargin
  simp [decision, hypos, hxpos]
