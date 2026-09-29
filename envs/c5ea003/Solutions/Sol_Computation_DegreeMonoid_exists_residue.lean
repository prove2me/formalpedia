-- Prove2me | solution 1 for Computation.DegreeMonoid.exists_residue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:02:23.5805+00:00
-- url     : https://prove2.me/submissions/1867f94e-e9e8-47f1-b0ce-9a8058f7283e

import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
theorem solution {p q : ℕ} (hp : 0 < p) (cop : Nat.Coprime q p) (n : ℕ) :
    ∃ b < p, (p : ℤ) ∣ (n : ℤ) - (b : ℤ) * (q : ℤ) := by
  haveI : NeZero p := ⟨by omega⟩
  -- `q` is a unit mod `p`; take `b ≡ n q⁻¹ (mod p)`
  let u := ZMod.unitOfCoprime q cop
  refine ⟨((n : ZMod p) * ↑u⁻¹).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  have hu : (q : ZMod p) = ↑u := (ZMod.coe_unitOfCoprime q cop).symm
  rw [hu, mul_assoc, Units.inv_mul, mul_one, sub_self]
