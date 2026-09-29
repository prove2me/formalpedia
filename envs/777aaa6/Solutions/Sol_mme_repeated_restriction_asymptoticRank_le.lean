-- Prove2me | solution 1 for mme_repeated_restriction_asymptoticRank_le
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:31.02422+00:00
-- url     : https://prove2.me/submissions/a9295f48-0398-463b-9536-99a37637f502

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_duality

open MME BigOperators
universe u
set_option autoImplicit false

/-- Restricting a repeated source preserves the multiplicity factor in an
asymptotic-rank upper bound. -/
theorem solution
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X Y : TensorObj K d} (copies r : ℕ)
    (hrestrict : TensorObj.Restrict X (TensorObj.bigAdd (fun _ : Fin copies => Y)))
    (hrank : tensorAsymptoticRank Y ≤ r) :
    tensorAsymptoticRank X ≤ copies * r := by
  let P := TensorQ.tensorStrassen K d hd
  rw [TensorQ.tensorAsymptoticRank_eq hd, mme_strassen_duality]
  apply ciSup_le
  intro phi
  have hq : P.le (TensorQ.toQ X)
      (TensorQ.toQ (TensorObj.bigAdd (fun _ : Fin copies => Y))) := hrestrict
  have hmono := phi.monotone' hq
  have hphi : phi (TensorQ.toQ Y) ≤ (r : ℝ) := by
    apply (P.eval_le_asymptoticRank (TensorQ.toQ Y) phi).trans
    simpa only [TensorQ.tensorAsymptoticRank_eq hd] using hrank
  calc
    phi (TensorQ.toQ X) ≤ phi (TensorQ.toQ (TensorObj.bigAdd (fun _ : Fin copies => Y))) := hmono
    _ = (copies : ℝ) * phi (TensorQ.toQ Y) := by
      rw [TensorQ.toQ_bigAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, map_mul, map_natCast]
    _ ≤ (copies : ℝ) * r := mul_le_mul_of_nonneg_left hphi (Nat.cast_nonneg copies)


#print axioms solution
