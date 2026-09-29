-- Prove2me | Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra
-- name    : Geometry_PythagoreanHydra_PythagoreanHydra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T13:06:18.59882+00:00
-- url     : https://prove2.me/theorems/ceda3c7c-479d-43d8-b830-47392aac5699
-- title:
--   Aether Catalog definitions — Geometry_PythagoreanHydra_PythagoreanHydra
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PythagoreanHydra.PythagoreanHydra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PythagoreanHydra/PythagoreanHydra.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame

/-!
# The Pythagorean Hydra

Hercules fights a hydra whose heads are **primitive Pythagorean triples**.  He chops one
head off; the hydra retaliates by regrowing finitely many heads, each of which is a
*Berggren ancestor* of the chopped head — i.e. obtained from it by a non-empty sequence of
inverse Berggren moves (`invA`, `invB`, `invC`, packaged in `PythHydra.parent`).  The
regrowth therefore follows the branching of the Berggren tree exactly, and the only head
that cannot retaliate is the root `(3,4,5)` (and, more generally, any head of hypotenuse
`≤ 5`).

Main results.

* `PythHydra.pythagorean_hydra_terminates` — Hercules always wins: no infinite battle,
  for arbitrary (even unbounded) regrowth.
* `PythHydra.pythagorean_hydra_length_le` — with branching bound `k`, every battle from
  `H` lasts at most `Phi k (H.map lvl)` moves, and this is attained
  (`longest_play_eq`), so the game length is *exactly* the potential.
* `PythHydra.pythagorean_hydra_elementary_bound` — an explicit elementary bound
  `N ≤ card H * (k+1)^(L+1)` where `L` bounds the hypotenuses.
* `PythHydra.root_battle_bound` — a completely concrete instance: a battle starting from
  the single head `(3,4,5)` with branching bound `3` lasts at most `364` moves.

**Calibration (the mission's "if false" branch).**  The Pythagorean Hydra is a *flat*
hydra: the Berggren descent assigns each head an ordinal `< ω` (its hypotenuse, or its
depth in the tree), so the whole game lives at `ω^ω` and its termination is proved here
by an explicit primitive recursive potential.  This is provably weaker than the
Kirby–Paris hydra, whose heads carry `ε₀`-many ordinals because regrowth may *copy
subtrees of unbounded height*.  In the Berggren tree the regrowth is always **downward**
(towards `(3,4,5)`), which is what caps the strength.  A Kirby–Paris phenomenon on the
Berggren tree therefore cannot arise from the descent structure alone: one would need a
regrowth rule producing heads of *greater* Berggren depth, which the inverse Berggren
moves never do.
-/

namespace PythHydra

/-- A head of the Pythagorean Hydra. -/
abbrev Tri := ℤ × ℤ × ℤ

/-- The level of a head: its hypotenuse. -/
def lvl (t : Tri) : ℕ := t.2.2.toNat

/-- One inverse-Berggren step: `s` is the Berggren parent of the (non-root) triple `t`. -/
def ParentStep (s t : Tri) : Prop :=
  IsPPT t.1 t.2.1 t.2.2 ∧ 5 < t.2.2 ∧ s = parent t.1 t.2.1 t.2.2

/-- `s` is a Berggren ancestor of `t`: reachable from `t` by inverse Berggren moves. -/
def IsBergAncestor (s t : Tri) : Prop := Relation.TransGen ParentStep s t




/-- **The Pythagorean Hydra move.**  A head `t` is chopped and at most `k` heads regrow,
each one a Berggren ancestor of `t`. -/
inductive BergChop (k : ℕ) : Multiset Tri → Multiset Tri → Prop
  | chop (t : Tri) (H R : Multiset Tri) (hR : ∀ s ∈ R, IsBergAncestor s t)
      (hcard : Multiset.card R ≤ k) : BergChop k (t ::ₘ H) (R + H)

/-- The same move with no bound on the number of regrown heads. -/
inductive BergChopU : Multiset Tri → Multiset Tri → Prop
  | chop (t : Tri) (H R : Multiset Tri) (hR : ∀ s ∈ R, IsBergAncestor s t) :
      BergChopU (t ::ₘ H) (R + H)



/-- A battle of exactly `N` moves. -/
def Battle (k : ℕ) : ℕ → Multiset Tri → Multiset Tri → Prop
  | 0, H, H' => H = H'
  | (n + 1), H, H' => ∃ M, BergChop k H M ∧ Battle k n M H'








end PythHydra


