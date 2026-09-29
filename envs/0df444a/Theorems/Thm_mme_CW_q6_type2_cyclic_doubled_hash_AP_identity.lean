-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_doubled_hash_AP_identity
-- name    : mme_CW_q6_type2_cyclic_doubled_hash_AP_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:02:34.893551+00:00
-- url     : https://prove2.me/theorems/efd35bc8-80d9-4549-8c55-74f3b9bf3bc4
-- title:
--   Arithmetic-progression hash identity for the cyclic q=6 type-2 family
-- statement:
--   For the cyclic product of three exact q=6 coupled-address families, assign independent doubled base hashes to the three orientations. Reweight the three cyclic hash triples by $(X,Y,Z)$, $(4Z,-2X,Y)$, and $(-2Y,4Z,X)$ and add them modewise. On every coordinatewise-supported mixture $(x,y,z)$, the combined hashes obey the arithmetic-progression identity $$H_0(x)+H_1(y)=2H_2(z).$$ This integral identity is the algebraic input for the type-2 Salem--Spencer retention rule.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; cyclic type-2 use of the Salem--Spencer hash.

import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_doubled_hash_AP_identity
    {R : Type} [CommRing R] {N L G : ℕ}
    (b : Fin 3 → R) (w : Fin 3 → Fin (2 * N) → R)
    (x y z : CWQ6Type2CyclicEdge N L G)
    (hsupp : CWQ6Type2CyclicCoordinatewiseSupported x y z) :
    let H0 := fun e : CWQ6Type2CyclicEdge N L G ↦ cwQ6DoubledXHash (b 0) (w 0) (e.1.1 0) + 4 * cwQ6DoubledZHash (b 1) (w 1) (e.2.1.1 2) - 2 * cwQ6DoubledYHash (b 2) (w 2) (e.2.2.1 1)
    let H1 := fun e : CWQ6Type2CyclicEdge N L G ↦ cwQ6DoubledYHash (b 0) (w 0) (e.1.1 1) - 2 * cwQ6DoubledXHash (b 1) (w 1) (e.2.1.1 0) + 4 * cwQ6DoubledZHash (b 2) (w 2) (e.2.2.1 2)
    let H2 := fun e : CWQ6Type2CyclicEdge N L G ↦ cwQ6DoubledZHash (b 0) (w 0) (e.1.1 2) + cwQ6DoubledYHash (b 1) (w 1) (e.2.1.1 1) + cwQ6DoubledXHash (b 2) (w 2) (e.2.2.1 0)
    H0 x + H1 y = 2 * H2 z := by
  sorry
