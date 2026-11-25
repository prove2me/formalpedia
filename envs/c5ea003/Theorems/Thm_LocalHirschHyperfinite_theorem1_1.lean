-- Prove2me | Theorems.Thm_LocalHirschHyperfinite_theorem1_1
-- name    : LocalHirschHyperfinite.theorem1_1
-- status  : Open
-- author  : @username
-- created : 2026-11-25T14:28:17.324641+00:00
-- url     : https://prove2.me/theorems/e34e74ba-f65f-5e51-8599-4cd7a3dd658f
-- title:
--   Theorem 1.1 — local finite Hirsch length implies hyperfiniteness
-- statement:
--   Let $G$ be countable, and suppose each finitely generated subgroup is virtually solvable of finite Hirsch length. For every Borel action of $G$ on a standard Borel space, the orbit relation is hyperfinite. The action is arbitrary, including actions with stabilizers. Local Hirsch lengths and finite indices can vary across subgroups.
-- source:
--   hyperfiniteness-and-finite-hirsch-length.tex, Theorem 1.1, lines 37–39. Supplied manuscript SHA-256 3fc959f77eef8bd2c0ac1349f4d875e7c83ce8d168bc63c39b4df2fcbdd966e0.

import Definitions.Def_LocalHirsch20261125

set_option autoImplicit false

theorem LocalHirschHyperfinite.theorem1_1 (G X : Type*)
    [Group G] [Countable G] [MulAction G X] [MeasurableSpace X] [StandardBorelSpace X]
    (hG : LocalHirschHyperfinite.IsLocallyVirtuallySolvableFiniteHirsch G)
    (hX : LocalHirschHyperfinite.BorelAction G X) :
    LocalHirschHyperfinite.IsHyperfinite (LocalHirschHyperfinite.orbitRel G (X := X)) := by sorry
