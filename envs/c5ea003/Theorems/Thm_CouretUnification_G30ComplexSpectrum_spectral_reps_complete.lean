-- Prove2me | Theorems.Thm_CouretUnification_G30ComplexSpectrum_spectral_reps_complete
-- name    : CouretUnification.G30ComplexSpectrum.spectral_reps_complete
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T17:23:08.159462+00:00
-- url     : https://prove2.me/theorems/e09983b9-754b-4189-a396-f9ac4925b46f
-- title:
--   Every enumerated triple has a listed Gaussian spectrum
-- statement:
--   Let $V=\{0,\ldots,7\}$, whose ordered unit labels are $(1,7,11,13,17,19,23,29)$. Their fixed $C_2\times C_4$ coordinates are $((0,0),(0,1),(1,2),(0,3),(1,3),(0,2),(1,1),(1,0))$. The list $\mathcal T$ enumerates increasing triples of distinct indices from $V$. For $(m,n)\in\{0,1\}\times\{0,1,2,3\}$ and coordinate $(a,b)$, use $\chi_{m,n}=(-1)^{ma}i^{nb}$ and $\lambda_{m,n}(T)=\sum_{x\in T}\chi_{m,n}(x)$, represented exactly as an integer pair in $\mathbb Z[i]$. Let the ordered representative list be $\mathcal R=([0,1,2],[0,1,3],[0,1,4],[0,1,5],[1,2,3],[1,2,4],[1,2,5],[1,2,6],[1,2,7],[1,3,5])$. Every $T\in\mathcal T$ has the same Gaussian spectral histogram as some listed representative: $$\forall T\in\mathcal T,\ \exists R\in\mathcal R,\ C(T)=C(R).$$ The histogram counts the eight character sums on the specified 49-point Gaussian grid. This is completeness within the 56 enumerated triples.
-- source:
--   https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/g30-gate-b-lean/G30ComplexSpectrum.lean#L129-L129; theorem CouretUnification.G30ComplexSpectrum.spectral_reps_complete; Proofs mechanically replaced by kernel decide using Lean-oracle declaration ranges; statement spans preserved. Validated in https://github.com/alexcour/couret-finite-verifications/actions/runs/42503615738

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

theorem spectral_reps_complete : repsComplete = true := by sorry




-- The two old power/energy classes: 32 and 24.












-- Group law in C2 x C4, represented with the same coordinates as the legacy file.












-- Exact witnesses produced independently by verify_g30_gate_b.py.




















end CouretUnification.G30ComplexSpectrum
