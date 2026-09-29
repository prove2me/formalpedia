-- Prove2me | Definitions.Def_mme_CW_q6_type2_cyclic_data
-- name    : mme_CW_q6_type2_cyclic_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T21:27:29.482249+00:00
-- url     : https://prove2.me/theorems/c80c86b4-c1ff-417a-b8fb-34085f337db2
-- title:
--   Cyclic type-2 address hypergraph for a four-edge constituent
-- statement:
--   Defines the three-cyclic-orientation exact-address hypergraph used in the type-2 Salem--Spencer extraction. Each edge contains three exact four-edge addresses; its mode vertices are the cyclicly aligned triples of their X, Y, and Z words. The bundled predicate records mode disjointness and inducedness.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 3.2, pp. 359-360, and Lemma 5.1(i), pp. 363-364.

import Definitions.Def_mme_CW_q6_primary_hash_family

namespace MME

set_option autoImplicit false

def CWQ6Type2CyclicEdge (N L G : ℕ) : Type :=
  CWQ6ExactCoupledAddress N L G × (CWQ6ExactCoupledAddress N L G × CWQ6ExactCoupledAddress N L G)

def CWQ6Type2CyclicModeWord (N : ℕ) : Type :=
  (Fin (2 * N) → Fin 3) × ((Fin (2 * N) → Fin 3) × (Fin (2 * N) → Fin 3))

def cwQ6Type2CyclicModeWord {N L G : ℕ} (e : CWQ6Type2CyclicEdge N L G) : Fin 3 → CWQ6Type2CyclicModeWord N
  | ⟨0, _⟩ => (e.1.1 0, (e.2.1.1 2, e.2.2.1 1))
  | ⟨1, _⟩ => (e.1.1 1, (e.2.1.1 0, e.2.2.1 2))
  | ⟨2, _⟩ => (e.1.1 2, (e.2.1.1 1, e.2.2.1 0))
  | ⟨n + 3, h⟩ => absurd h (by omega)

def CWQ6Type2CyclicCoordinatewiseSupported {N L G : ℕ} (x y z : CWQ6Type2CyclicEdge N L G) : Prop :=
  CWQ6CoupledCoordinatewiseSupported (cwQ6CoupledMixedAddress x.1.1 y.1.1 z.1.1) ∧
  CWQ6CoupledCoordinatewiseSupported (cwQ6CoupledMixedAddress y.2.1.1 z.2.1.1 x.2.1.1) ∧
  CWQ6CoupledCoordinatewiseSupported (cwQ6CoupledMixedAddress z.2.2.1 x.2.2.1 y.2.2.1)

def CWQ6Type2CyclicInducedModeDisjoint {N L G : ℕ} (F : Finset (CWQ6Type2CyclicEdge N L G)) : Prop :=
  (∀ i : Fin 3, Function.Injective (fun e : F ↦ cwQ6Type2CyclicModeWord e.1 i)) ∧
  ∀ x y z : F, CWQ6Type2CyclicCoordinatewiseSupported x.1 y.1 z.1 → x = y ∧ y = z

end MME


