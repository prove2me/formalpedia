-- Prove2me | Theorems.Thm_isSimplyConnected_unitDisc
-- name    : isSimplyConnected_unitDisc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T18:49:01.214987+00:00
-- url     : https://prove2.me/theorems/108cd385-36d9-4db4-bc71-f579eb635d3a
-- title:
--   The complex unit disc is simply connected
-- statement:
--   **The unit disc is simply connected.** With its usual topology as an open subset of $\mathbb C$, the open unit disc $\mathbb D=\{z\in\mathbb C:|z|<1\}$ is simply connected: it is path connected, and every loop in it is homotopic, within the disc, to the constant loop at its basepoint.
--
--   The reason is that the disc is convex, hence star-shaped about the origin: the straight-line path $t\mapsto(1-t)z_0+tz_1$ between any two of its points stays inside it, since $|(1-t)z_0+tz_1|\le(1-t)|z_0|+t|z_1|<1$ for $t\in[0,1]$. Contracting a loop $p$ by $F(t,s)=(1-s)p(t)+sz_0$ then gives a homotopy to the constant loop that never leaves the disc.
--
--   This is recorded as a standalone statement because it is a genuine ingredient rather than a routine step. The covering-space lifting theorem available in the environment (`Mathlib.Topology.Homotopy.Lifting`, used in `Mathlib/Analysis/Complex/BranchLogRoot.lean`) demands a `[SimplyConnectedSpace A]` instance on the domain, and the pinned Mathlib contains no lemma deriving `IsSimplyConnected` of a convex set in general, so the fact has to be established directly. It is the one missing hypothesis needed to lift a map defined on the disc through a covering map such as $z\mapsto e^z$, which is the first step of Schottky's theorem as used in the escape argument of Milnor's Theorem 3.7 (Montel's theorem).
--
--   **Formalization Note.** The statement is deliberately phrased for the open disc of radius `1` about the origin, which is the disc that appears throughout the Schottky estimates (`MilnorDynamics.schottky_two_point` `bd23b2a7`, `MilnorDynamics.schottky_bound` `ad33741e`). It is stated in the root namespace, not in `MilnorDynamics`, because it is a fact about the standard disc rather than a statement of Milnor's theorem. The general characterisation is `IsSimplyConnected.isSimplyConnected_iff_exists_homotopy_refl_forall_mem` (`Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:167`), and convexity of balls is `convex_ball`; the point of this target is to supply the homotopy in closed form.
-- source:
--   Standard topology of the complex plane: the open unit disc is convex, hence simply connected. Used as the simply-connected hypothesis for covering-space lifting through the exponential in the proof of Schottky's theorem (Milnor, Dynamics in One Complex Variable, 3rd ed., Section 3).

import Mathlib

import Mathlib

open Set

theorem isSimplyConnected_unitDisc : IsSimplyConnected (Metric.ball 0 1 : Set ℂ) := by sorry
