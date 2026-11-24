-- Prove2me | solution 1 for FHENoise.bgv_mul_noise_bound
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:41:31.745248+00:00
-- url     : https://prove2.me/submissions/f4d775a3-8e05-401c-b240-6315a916ec47

import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth
import Definitions.Def_Cryptography_FHE_RingLWE

open FHENoise

variable {R : Type*} [CommRing R]
variable (G : NoiseGauge R)

namespace FHENoise.NoiseGauge

lemma gamma_pos : 0 < G.gamma := lt_of_lt_of_le zero_lt_one G.gamma_one_le

lemma gamma_nonneg : 0 ≤ G.gamma := le_of_lt G.gamma_pos

end FHENoise.NoiseGauge

namespace FHENoise.NoiseGauge

lemma nu_mul_le_bounds {x y : R} {a b : ℝ} (hx : G.nu x ≤ a) (hy : G.nu y ≤ b) :
    G.nu (x * y) ≤ G.gamma * a * b := by
  have hx0 := G.nu_nonneg x
  have hy0 := G.nu_nonneg y
  have ha : 0 ≤ a := le_trans hx0 hx
  calc G.nu (x * y) ≤ G.gamma * G.nu x * G.nu y := G.nu_mul_le x y
    _ ≤ G.gamma * a * G.nu y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx G.gamma_nonneg) hy0
    _ ≤ G.gamma * a * b := mul_le_mul_of_nonneg_left hy (mul_nonneg G.gamma_nonneg ha)

end FHENoise.NoiseGauge

theorem solution (t m e m' e' : R) {mu mu' eps eps' tau : ℝ}
    (hm : G.nu m ≤ mu) (hm' : G.nu m' ≤ mu') (he : G.nu e ≤ eps)
    (he' : G.nu e' ≤ eps') (ht : G.nu t ≤ tau) :
    G.nu (e * m' + m * e' + t * (e * e')) ≤
      G.gamma * (eps * mu' + mu * eps') + G.gamma ^ 2 * tau * (eps * eps') := by
  have hnn := G.nu_nonneg
  have h1 : G.nu (e * m') ≤ G.gamma * eps * mu' := G.nu_mul_le_bounds he hm'
  have h2 : G.nu (m * e') ≤ G.gamma * mu * eps' := G.nu_mul_le_bounds hm he'
  have hee : G.nu (e * e') ≤ G.gamma * eps * eps' := G.nu_mul_le_bounds he he'
  have h3 : G.nu (t * (e * e')) ≤ G.gamma * tau * (G.gamma * eps * eps') :=
    G.nu_mul_le_bounds ht hee
  have hsum := G.nu_add_le (e * m' + m * e') (t * (e * e'))
  have hsum2 := G.nu_add_le (e * m') (m * e')
  have hring1 : G.gamma * eps * mu' + G.gamma * mu * eps' =
      G.gamma * (eps * mu' + mu * eps') := by ring
  have hring2 : G.gamma * tau * (G.gamma * eps * eps') =
      G.gamma ^ 2 * tau * (eps * eps') := by ring
  linarith
