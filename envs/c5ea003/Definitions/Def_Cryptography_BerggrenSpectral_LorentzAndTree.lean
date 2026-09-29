-- Prove2me | Definitions.Def_Cryptography_BerggrenSpectral_LorentzAndTree
-- name    : Cryptography_BerggrenSpectral_LorentzAndTree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:11:57.811781+00:00
-- url     : https://prove2.me/theorems/34df0b7c-ef2e-4e97-9244-2f0b2c99b1ae
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenSpectral_LorentzAndTree
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenSpectral.LorentzAndTree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenSpectral/LorentzAndTree.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenSpectral_SpectrumAndTrace

/-!
# Cross-Domain Bridge: Lorentz Structure of the Tree and Periodicity of Triples mod `p`

Third research cycle.  The resonance theorems of the previous files are statements about the
Berggren matrices as abstract elements of `GL₃`.  Here we connect them back to the object the
Berggren tree is *about* — primitive Pythagorean triples — through the Lorentz form
`Q(a,b,c) = a² + b² - c²`.

## Main results

* `berg_isometry_one/two/three` : over **any** commutative ring, `Mᵢᵀ Q Mᵢ = Q`, i.e. the three
  Berggren generators lie in the orthogonal group `O(2,1)` of the Pythagorean form.  This is
  the structural reason the tree maps triples to triples.
* `berg_preserves_pythagorean` : consequently `Mᵢ` maps Pythagorean triples to Pythagorean
  triples, reproving (from the group-theoretic reason rather than by expansion) the catalog
  fact underlying `Shared/BerggrenTrees`.
* `berg_form_preserved_mod` : the same identity holds after reduction mod `N`, so the
  Berggren dynamics on `(ZMod N)³` preserves the conic `a² + b² = c²`.
* `berg_tree_period_mod_p` : for every odd prime `p` and **every** vector `v`, the hyperbolic
  branch is periodic mod `p` with period dividing `p² - 1`; in particular the root triple
  `(3,4,5)` returns to itself.  The "resonant energy frequency" is thus visible directly on
  the tree of triples, not only on the matrices.
* `berg_semiprime_period` : for `N = p q` the period divides `lcm (p² - 1, q² - 1)` — a
  Carmichael-type bound whose *failure to be attained simultaneously at both primes* is
  exactly what `Factorization.lean` exploits.
-/

namespace BerggrenSpectral

open Matrix

variable (R : Type*) [CommRing R]

/-- The Lorentz/Pythagorean form `diag (1, 1, -1)`. -/
def pythQ : Matrix (Fin 3) (Fin 3) R := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

variable {R}

/-- Generic versions of the generators over an arbitrary commutative ring. -/
def M1R : Matrix (Fin 3) (Fin 3) R := !![1, -2, 2; 2, -1, 2; 2, -2, 3]

/-- Generic version of the third generator over an arbitrary commutative ring. -/
def M3R : Matrix (Fin 3) (Fin 3) R := !![-1, 2, 2; -2, 1, 2; -2, 2, 3]




/-! ## Preservation of the Pythagorean conic -/

/-- The quadratic form attached to a triple. -/
def pythForm (v : Fin 3 → R) : R := v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2






/-! ## Periodicity of the tree dynamics mod `p` -/

variable (p : ℕ) [Fact p.Prime]




end BerggrenSpectral


