-- Prove2me | solution 1 for CouretUnification.G30ComplexSpectrum.tc_iso_target3
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T17:27:31.14573+00:00
-- url     : https://prove2.me/submissions/428c4c04-4a4e-4411-bb7b-9b847befb347

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












-- Group law in C2 x C4, represented with the same coordinates as the legacy file.












-- Exact witnesses produced independently by verify_g30_gate_b.py.















theorem p2m_local_tc_iso_target3 : graphIsoCert TC tcTarget3 p3 = true := by decide




end CouretUnification.G30ComplexSpectrum

theorem solution : @Eq.{1} Bool
  (CouretUnification.G30ComplexSpectrum.graphIsoCert CouretUnification.G30ComplexSpectrum.TC
    CouretUnification.G30ComplexSpectrum.tcTarget3 CouretUnification.G30ComplexSpectrum.p3)
  Bool.true := @_root_.CouretUnification.G30ComplexSpectrum.p2m_local_tc_iso_target3

