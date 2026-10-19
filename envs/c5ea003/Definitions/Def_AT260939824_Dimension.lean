-- Prove2me | Definitions.Def_AT260939824_Dimension
-- name    : AT260939824_Dimension
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:41:19.377995+00:00
-- url     : https://prove2.me/theorems/ad43d5d6-4bcc-4a5c-9458-f1795fb33f54
-- title:
--   Signed lattice directions and edge laws
-- statement:
--   A signed direction in a natural dimension $m$ consists of an axis in $\{0,\ldots,m-1\}$ and a Boolean sign. It determines the positive or negative standard integer lattice vector on that axis. For a simple graph $H$, direction-law data assign such a direction to each oriented edge, reverse vectors on reversed edges, give zero vector sum around every closed four-walk, and require uniqueness of the middle vertex for the specified straight two-edge configurations.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/Dimension.lean, selected declaration lines 29-33, 35-37, 138-154; SHA-256 507595dd7b3d9cf5560d2253512c68ed8cea14b37ba100a0d02f87dbec1f3d72. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Checked parts of the dimension argument

This file proves the finite-axis counting step of Lemma 7.4, the odd-sum
step and invariant-coloring step of Lemma 7.6, and the final parity split
in Proposition 7.7 of arXiv:2609.39824v1.

`proposition7_7_of_finite_source_obstructions` is explicitly conditional:
the marker graph construction, twelve-tile source extraction, full
rigidity lemma and odd-product obstruction are inputs. They are not
asserted as axioms, and this file does not prove those inputs.
The actual inputs are established in the later marker, twelve-tile,
source-extraction, and odd-product modules. The complete requested result
is `proposition7_7` in `Proposition77.lean`.
-/

namespace AbelianTargets

open scoped BigOperators Pointwise

/-- A signed standard direction, together with its unsigned target axis. -/
structure SignedDirection (m : ℕ) where
  axis : Fin m
  positive : Bool
  deriving DecidableEq

/-- The integer vector corresponding to a signed direction. -/
def SignedDirection.vector {m : ℕ} (s : SignedDirection m) : Lattice m :=
  if s.positive then unitVector s.axis else -unitVector s.axis



















/-- Edge-direction hypotheses preceding Lemma 7.3. Proof-dependent edge
arguments keep the map defined only on actual oriented graph edges. -/
structure DirectionLaws {V : Type*} (H : SimpleGraph V) (m : ℕ) where
  direction : ∀ {u v : V}, H.Adj u v → SignedDirection m
  reverse : ∀ {u v : V} (h : H.Adj u v),
    (direction h.symm).vector = -(direction h).vector
  four_walk : ∀ {u v w z : V}
    (huv : H.Adj u v) (hvw : H.Adj v w)
    (hwz : H.Adj w z) (hzu : H.Adj z u),
    (direction huv).vector + (direction hvw).vector +
      (direction hwz).vector + (direction hzu).vector = 0
  straight_middle_unique : ∀ {u v v' w : V}
    (huv : H.Adj u v) (hvw : H.Adj v w)
    (huv' : H.Adj u v') (hv'w : H.Adj v' w),
    direction huv = direction hvw →
    direction huv = direction huv' →
    direction huv = direction hv'w → v = v'





end AbelianTargets


