-- Prove2me | solution 1 for CouretUnification.G30ComplexSpectrum.tc_fiber_size
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T17:24:52.029384+00:00
-- url     : https://prove2.me/submissions/f4165200-8029-4886-9f1b-03a7f84f3616

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








theorem p2m_local_tc_fiber_size : tcFiber.length = 5 := by decide



-- Group law in C2 x C4, represented with the same coordinates as the legacy file.












-- Exact witnesses produced independently by verify_g30_gate_b.py.




















end CouretUnification.G30ComplexSpectrum

theorem solution : @Eq.{1} Nat
  (@List.length.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V) CouretUnification.G30ComplexSpectrum.tcFiber)
  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) := @_root_.CouretUnification.G30ComplexSpectrum.p2m_local_tc_fiber_size

