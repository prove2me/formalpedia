-- Prove2me | solution 1 for CouretUnification.G30ComplexSpectrum.tc_fiber_members
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T17:25:17.998918+00:00
-- url     : https://prove2.me/submissions/6d64d978-1143-4301-affc-be13c71316c5

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










theorem p2m_local_tc_fiber_members :
    tcFiber = [[0,1,3], [0,2,5], [0,2,7], [0,4,6], [0,5,7]] := by decide

-- Group law in C2 x C4, represented with the same coordinates as the legacy file.












-- Exact witnesses produced independently by verify_g30_gate_b.py.




















end CouretUnification.G30ComplexSpectrum

theorem solution : @Eq.{1} (List.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V)) CouretUnification.G30ComplexSpectrum.tcFiber
  (@List.cons.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V)
    (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
      (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 0)
        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 0)))
      (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
        (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 1)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 1)))
        (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
          (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 3)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 3)))
          (@List.nil.{0} CouretUnification.G30ComplexSpectrum.V))))
    (@List.cons.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V)
      (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
        (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 0)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 0)))
        (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
          (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 2)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 2)))
          (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
            (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 5)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 5)))
            (@List.nil.{0} CouretUnification.G30ComplexSpectrum.V))))
      (@List.cons.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V)
        (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
          (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 0)))
          (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
            (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 2)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 2)))
            (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
              (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 7)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 7)))
              (@List.nil.{0} CouretUnification.G30ComplexSpectrum.V))))
        (@List.cons.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V)
          (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
            (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 0)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 0)))
            (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
              (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 4)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 4)))
              (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
                (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 6)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 6)))
                (@List.nil.{0} CouretUnification.G30ComplexSpectrum.V))))
          (@List.cons.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V)
            (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
              (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 0)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 0)))
              (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
                (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 5)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 5)))
                (@List.cons.{0} CouretUnification.G30ComplexSpectrum.V
                  (@OfNat.ofNat.{0} CouretUnification.G30ComplexSpectrum.V (nat_lit 7)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 7)))
                  (@List.nil.{0} CouretUnification.G30ComplexSpectrum.V))))
            (@List.nil.{0} (List.{0} CouretUnification.G30ComplexSpectrum.V))))))) := @_root_.CouretUnification.G30ComplexSpectrum.p2m_local_tc_fiber_members

