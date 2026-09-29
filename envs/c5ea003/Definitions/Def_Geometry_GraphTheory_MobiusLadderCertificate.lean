-- Prove2me | Definitions.Def_Geometry_GraphTheory_MobiusLadderCertificate
-- name    : Geometry_GraphTheory_MobiusLadderCertificate
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:08.509064+00:00
-- url     : https://prove2.me/theorems/59da1397-f67f-4d5a-a068-d07cb91c03e6
-- title:
--   Aether Catalog definitions — Geometry_GraphTheory_MobiusLadderCertificate
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GraphTheory.MobiusLadderCertificate`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GraphTheory/MobiusLadderCertificate.lean by skeleton subtraction
import Mathlib

/-!
# An explicit Möbius-ladder symmetry certificate for a cubic edge-transitive graph

The *Möbius ladder* `Mₙ` is the cubic graph on `2n` vertices obtained from the
cycle `C₂ₙ` (the "rim", edges `i ∼ i±1`) by adding the `n` "rungs" `i ∼ i+n`.
The whole family is vertex-transitive, but it is **not** edge-transitive in
general: for `n ≥ 4` the rim edges and the rung edges lie in distinct orbits of
the automorphism group.  The small Möbius ladders that *are* edge-transitive are
`M₂ ≅ K₄` and `M₃ ≅ K₃,₃`.

This file gives a fully verified, **explicit symmetry certificate** for the
edge-transitive Möbius ladder `M₃` on the six vertices `ZMod 6`:

* `MobiusLadder3`  — the Möbius ladder `M₃`, defined faithfully from its rim
  edges `i ∼ i+1` and rungs `i ∼ i+3`.
* `MobiusLadder3.cubic`  — every vertex has degree `3` (the graph is cubic).
* `MobiusLadder3.adj_iff_parity`  — the computational identification
  `M₃ ≅ K₃,₃`: two vertices are adjacent iff they have opposite parity.
* `edge_transitive`  — the graph is edge-transitive: any edge can be carried to
  any other edge by a vertex permutation preserving adjacency.
* `vertex_transitive`  — the graph is vertex-transitive (via rotations).

## Resolving circular dependencies by direct computation

Edge-transitivity is often argued through the structure theory of the
automorphism group, which on a small graph is circular (the group is defined
via the very symmetries one is trying to exhibit).  Here we sidestep that by a
*certificate*: a concrete finite list `MobiusLadder3.cert` of vertex
permutations, each **checked by `decide` to preserve adjacency**
(`cert_isSym`), whose orbit of a single base edge **provably exhausts every
edge** (`cert_covers`).  General edge-transitivity then follows from the fact
that adjacency-preserving permutations form a group (`isSym_one`, `isSym_mul`,
`isSym_inv`).  All finite facts are discharged by kernel computation.
-/

namespace MobiusLadderCertificate

open SimpleGraph

/-- Vertex adjacency of the Möbius ladder `M₃` on `ZMod 6`: the rim edges
`i ∼ i+1` of the `6`-cycle together with the three rungs `i ∼ i+3`. -/
def adj3 (i j : ZMod 6) : Prop := j = i + 1 ∨ i = j + 1 ∨ j = i + 3

instance : DecidableRel adj3 :=
  fun i j => inferInstanceAs (Decidable (j = i + 1 ∨ i = j + 1 ∨ j = i + 3))

theorem adj3_symm : Symmetric adj3 := by intro x y; revert x y; decide

/-- The Möbius ladder `M₃`, a cubic graph on the six vertices `ZMod 6`. -/
def MobiusLadder3 : SimpleGraph (ZMod 6) where
  Adj := adj3
  symm := adj3_symm
  loopless := ⟨by decide⟩

instance : DecidableRel MobiusLadder3.Adj := inferInstanceAs (DecidableRel adj3)




/-- A vertex permutation is a **symmetry** of `M₃` iff it preserves adjacency in
both directions (equivalently, is an automorphism of the graph). -/
def IsSym (σ : Equiv.Perm (ZMod 6)) : Prop :=
  ∀ i j, MobiusLadder3.Adj (σ i) (σ j) ↔ MobiusLadder3.Adj i j

instance (σ : Equiv.Perm (ZMod 6)) : Decidable (IsSym σ) := by
  unfold IsSym; infer_instance




/-! ### The explicit symmetry certificate -/

/-- A fixed base edge of `M₃`. -/
def baseEdge : Sym2 (ZMod 6) := s(0, 1)

/-- The explicit symmetry certificate: nine adjacency-preserving permutations
whose images of `baseEdge` run over all nine edges of `M₃`.  Each permutation is
a product of transpositions that move only even vertices among themselves and
only odd vertices among themselves, hence preserves the bipartition. -/
def cert : List (Equiv.Perm (ZMod 6)) :=
  [1,
   Equiv.swap 1 3, Equiv.swap 1 5,
   Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 2 * Equiv.swap 1 5,
   Equiv.swap 0 4, Equiv.swap 0 4 * Equiv.swap 1 3, Equiv.swap 0 4 * Equiv.swap 1 5]



/-! ### Main symmetry theorems -/




end MobiusLadderCertificate


