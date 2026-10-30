-- Prove2me | Theorems.Thm_planar_simple_arc_complement_dense
-- name    : planar_simple_arc_complement_dense
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T01:19:26.989041+00:00
-- url     : https://prove2.me/theorems/9eb77d69-3110-4a6f-a3f0-9d1e9d0d84a7
-- title:
--   The complement of a planar simple arc is dense
-- statement:
--   Let $a:[0,1]\to\mathbb R^2$ be continuous and injective. Then
--
--   $$\overline{\mathbb R^2\setminus a([0,1])}=\mathbb R^2.$$
--
--   Equivalently, the image of a planar simple arc has empty interior. The result supplies the density needed to compare complement components after an arc is attached to a compact planar set.
-- source:
--   Bernal-González, Jiménez-Rodríguez, Muñoz-Fernández and Seoane-Sepúlveda, Non-Lipschitz Differentiable Functions on Slit Domains (2017), Remark 4.3(2), https://idus.us.es/bitstreams/90d7ee66-e877-4963-b925-80f7b92a1536/download . Supporting lemma for https://prove2.me/theorems/499509f0-5564-4ad2-b052-bdaa0fac6f2b

import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue

open Set

theorem planar_simple_arc_complement_dense (a : ℝ → ℝ × ℝ) (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1)) : Dense (a '' Set.Icc (0 : ℝ) 1)ᶜ := by sorry
