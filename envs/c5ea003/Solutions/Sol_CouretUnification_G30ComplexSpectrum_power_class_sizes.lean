-- Prove2me | solution 1 for CouretUnification.G30ComplexSpectrum.power_class_sizes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T17:23:00.148939+00:00
-- url     : https://prove2.me/submissions/c5389be9-80e7-4dcb-98cf-5227a9b9da8f

import Definitions.Def_Couret_G30ComplexSpectrum_e168a30c6229
import Mathlib.Tactic
import Mathlib.Tactic
set_option maxHeartbeats 0

set_option autoImplicit false
set_option maxRecDepth 1000000

/-!
Gate B candidate formalization for the 56 three-subsets of U(30).

Scope:
* exact finite complex Fourier spectra over Gaussian integers;
* ten spectral classes, certified by ten explicit representatives;
* power-profile classes 32/24;
* exact complex spectral fiber of T_C = {1,11,29}, of size 5;
* explicit graph-isomorphism certificates for the five members of that fiber.

Status on 2026-10-07:
P-SCAFFOLD. This file was generated after an independent exact Python replay, but
was NOT compiled in the present execution environment because no Lean binary is
installed there. Promotion to D-Lean requires a pinned Lean/Mathlib build and an
archived build log + SHA-256 manifest.

No RH, Hilbert-Polya, prime-distribution, or asymptotic claim is made here.
-/

namespace CouretUnification.G30ComplexSpectrum

































-- Every Fourier sum of a 3-set lies in [-3,3]^2.














-- One representative per exact complex spectral class, in lexicographic order.
















-- The two old power/energy classes: 32 and 24.



theorem p2m_local_power_class_sizes : powerReps.map powerClassSize = [32,24] := by decide








-- Group law in C2 x C4, represented with the same coordinates as the legacy file.












-- Exact witnesses produced independently by verify_g30_gate_b.py.




















end CouretUnification.G30ComplexSpectrum

theorem solution : @Eq.{1} (List.{0} Nat)
  (@List.map.{0, 0} (List.{0} CouretUnification.G30ComplexSpectrum.V) Nat
    CouretUnification.G30ComplexSpectrum.powerClassSize CouretUnification.G30ComplexSpectrum.powerReps)
  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))
    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) (@List.nil.{0} Nat))) := @_root_.CouretUnification.G30ComplexSpectrum.p2m_local_power_class_sizes

