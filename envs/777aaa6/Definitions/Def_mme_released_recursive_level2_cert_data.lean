-- Prove2me | Definitions.Def_mme_released_recursive_level2_cert_data
-- name    : mme_released_recursive_level2_cert_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T23:22:17.133891+00:00
-- url     : https://prove2.me/theorems/95574ecd-9286-4b48-af85-a1956a33d7ba
-- title:
--   Per-region certificate data for level-two entropy floors
-- statement:
--   Assembles the four parts of the per-region certificate data into lookups: the parametric mode of a region, its reference exponent table, and the numerator of its certified entropy floor over ten to the thirtieth.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Definitions.Def_mme_released_recursive_level2_cert_parta
import Definitions.Def_mme_released_recursive_level2_cert_partb
import Definitions.Def_mme_released_recursive_level2_cert_partc
import Definitions.Def_mme_released_recursive_level2_cert_partd

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MME.L2Cert

def certTab : List (List (Nat × (Int × Int × Int × Int) × (Int × Int × Int × Int) × Int)) :=
  [certRaw_0, certRaw_1, certRaw_2, certRaw_3, certRaw_4, certRaw_5, certRaw_6, certRaw_7,
   certRaw_8, certRaw_9, certRaw_10, certRaw_11]

def certAt (r : Fin 1104) : Nat × (Int × Int × Int × Int) × (Int × Int × Int × Int) × Int :=
  (certTab.getD (r.val / 92) []).getD (r.val % 92) (0, (0, 0, 0, 0), (0, 0, 0, 0), 0)

/-- The parametric mode of a region. -/
def certMode (r : Fin 1104) : Fin 3 := ⟨(certAt r).1 % 3, Nat.mod_lt _ (by decide)⟩

/-- The reference exponent table of a region. -/
def certE (r : Fin 1104) : Fin 3 → Fin 4 → Int := fun a j ↦
  let t := if a.val = 1 then (certAt r).2.2.1 else (certAt r).2.1
  if j.val = 0 then t.1 else if j.val = 1 then t.2.1 else if j.val = 2 then t.2.2.1 else t.2.2.2

/-- The numerator of the certified entropy floor of a region, over `10 ^ 30`. -/
def certNum (r : Fin 1104) : Int := (certAt r).2.2.2

end MME.L2Cert


