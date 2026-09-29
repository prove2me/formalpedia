-- Prove2me | Definitions.Def_Cryptography_ResidueDial_Converse
-- name    : Cryptography_ResidueDial_Converse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:23.203423+00:00
-- url     : https://prove2.me/theorems/4154f39a-a47e-4bf9-a198-66559a403b23
-- title:
--   Aether Catalog definitions — Cryptography_ResidueDial_Converse
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ResidueDial.Converse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ResidueDial/Converse.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Battery

/-!
# The converse capstone: structure blindness, factor blindness, and the cap

This file collects the *converse* statements: not "here is a dial that helps",
but "no dial of any kind helps beyond `4/3`", and — more sharply — "the internal
structure of the dial is invisible to the law".

## Lemma B2 (structure blindness)

`speedup_blind_to_structure`, `fiber_dial_speedup_eq_of_card_eq`: two dials of
equal density have *identical* speedup, whatever their internal structure.  In
particular a dial built by mixing character fibres — the `n = 3`, `n = 5` cubic
and quintic residue readings, or any reading into `n` symbols
(`symbolDial`) — cannot beat a plain half-density set, and half-density symbol
dials attain the cap exactly (`symbolDial_speedup_eq_four_thirds`).

## Corollary A2 (which-factor blindness is an identity)

For a semiprime `N = p·q` with `N ≡ c (mod M)`, the classes of `p` and `q` are
exchanged by the involution `u ↦ c·u⁻¹` (`factorSwap`,
`factorSwap_apply_of_mul_eq`).  Since densities are invariant under this
bijection (`density_image_factorSwap`), reading a dial against `p` and reading
it against `q` give *exactly* the same speedup (`which_factor_blind`): the
which-factor blindness observed empirically is an identity, not an
approximation.

## The capstone

`residue_dial_converse`: every residue dial, every fibre/character dial, and
every CRT battery is capped by `4/3`, strictly below the asked barrier `2`; and
`cap_attained_iff_half_density` pins down exactly when the cap is met.
-/

namespace ResidueDial

open Finset

variable {M : ℕ} [NeZero M]

/-! ## Density in terms of cardinality -/



/-! ## Lemma B2: the law is blind to the dial's internal structure -/



/-! ## Character / symbol dials: `n = 3`, `n = 5`, and all the rest -/

open scoped Classical in
/-- A *symbol dial*: read each residue class through a reading
`f : (ZMod M)ˣ → S` (a character, a power-residue symbol, a tuple of several
such readings) and keep the classes whose symbol lies in `T`. -/
noncomputable def symbolDial {S : Type*} (f : (ZMod M)ˣ → S) (T : Finset S) :
    Finset (ZMod M)ˣ :=
  (univ : Finset (ZMod M)ˣ).filter (fun u => f u ∈ T)







/-! ## Corollary A2: which-factor blindness as an identity -/

/-- The involution exchanging the two factors of a semiprime: if `p·q ≡ c`
modulo `M`, then the class of `q` is `c` times the inverse of the class of
`p`. -/
def factorSwap (c : (ZMod M)ˣ) : (ZMod M)ˣ ≃ (ZMod M)ˣ where
  toFun u := c * u⁻¹
  invFun u := c * u⁻¹
  left_inv u := by simp [mul_inv_rev]
  right_inv u := by simp [mul_inv_rev]





/-! ## Positional and interval witnesses -/


open scoped Classical in
/-- An *interval dial*: keep the scan positions lying in `[a, b)`. -/
noncomputable def intervalDial (n a b : ℕ) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun i => a ≤ (i : ℕ) ∧ (i : ℕ) < b)


/-! ## The capstone -/




end ResidueDial


