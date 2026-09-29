-- Prove2me | solution 1 for mme_more_asymmetry_global_region_six_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:52:55.830047+00:00
-- url     : https://prove2.me/submissions/b395a49e-aa0a-4aa6-8205-6fef348050e1

import Definitions.Def_mme_more_asymmetry_rational_global_entropy_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Theorems.Thm_mme_modern_entropyNat_upper_from_positive_reference
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open MME.MoreAsymmetryGlobalWitness BigOperators Finset
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private theorem log_cert_0 :
    (logLower 5 0 : ℝ) ≤ Real.log (reference 5 0 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (119922719/1000000000000000) (182637939/61217794189) (-7968209155097671/500000000000000) 0 23 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 0 = (-7968209155097671/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (-373166600552711/100000000000000) + (-920527302522503/250000000000000) -
      (79311/50000000000) = (-7968209155097671/500000000000000)
    norm_num
  have hRef : reference 5 0 = (119922719/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_1 :
    (logLower 5 1 : ℝ) ≤ Real.log (reference 5 1 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (413709729/25000000000000) (515840039/12722871289) (-2752305845352253/250000000000000) 0 16 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 1 = (-2752305845352253/250000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (-135628182013/80000000000) + (-197807002917073/250000000000000) -
      (79311/50000000000) = (-2752305845352253/250000000000000)
    norm_num
  have hRef : reference 5 1 = (413709729/25000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_2 :
    (logLower 5 2 : ℝ) ≤ Real.log (reference 5 2 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (247496221651/500000000000000) (3355596651/491636846651) (-1902742411946477/250000000000000) 0 11 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 2 = (-1902742411946477/250000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (36721840469811/1000000000000000) + (874951606322501/1000000000000000) -
      (79311/50000000000) = (-1902742411946477/250000000000000)
    norm_num
  have hRef : reference 5 2 = (247496221651/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_3 :
    (logLower 5 3 : ℝ) ≤ Real.log (reference 5 3 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4628903006557/1000000000000000) (722653006557/8535153006557) (-5375436956803879/1000000000000000) 0 8 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 3 = (-5375436956803879/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (333091980134319/250000000000000) + (362967643447413/200000000000000) -
      (79311/50000000000) = (-5375436956803879/1000000000000000)
    norm_num
  have hRef : reference 5 3 = (4628903006557/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_4 :
    (logLower 5 4 : ℝ) ≤ Real.log (reference 5 4 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (2504916817437/200000000000000) (942416817437/4067416817437) (-2190031712696311/500000000000000) 0 7 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 4 = (-2190031712696311/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (129538544282907/62500000000000) + (1034981480329543/500000000000000) -
      (79311/50000000000) = (-2190031712696311/500000000000000)
    norm_num
  have hRef : reference 5 4 = (2504916817437/200000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_5 :
    (logLower 5 5 : ℝ) ≤ Real.log (reference 5 5 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (2299931936023/500000000000000) (346806936023/4253056936023) (-5381730155176497/1000000000000000) 0 8 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 5 = (-5381730155176497/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (906589587497413/500000000000000) + (1327733764406897/1000000000000000) -
      (79311/50000000000) = (-5381730155176497/1000000000000000)
    norm_num
  have hRef : reference 5 5 = (2299931936023/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_6 :
    (logLower 5 6 : ℝ) ≤ Real.log (reference 5 6 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (488439504203/1000000000000000) (158254203/976720754203) (-7624296520558367/1000000000000000) 0 11 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 6 = (-7624296520558367/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (865853967735169/1000000000000000) + (8123151571171/250000000000000) -
      (79311/50000000000) = (-7624296520558367/1000000000000000)
    norm_num
  have hRef : reference 5 6 = (488439504203/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_7 :
    (logLower 5 7 : ℝ) ≤ Real.log (reference 5 7 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (16475961833/1000000000000000) (2434345541/63469501791) (-11013609700540131/1000000000000000) 0 16 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 7 = (-11013609700540131/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (-99424055919553/125000000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-11013609700540131/1000000000000000)
    norm_num
  have hRef : reference 5 7 = (16475961833/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_8 :
    (logLower 5 8 : ℝ) ≤ Real.log (reference 5 8 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (5987187/50000000000000) (27363863/12234395113) (-1593791509702401/100000000000000) 0 23 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 8 = (-1593791509702401/100000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1870425839691111/500000000000000) +
      (-1841052662875091/500000000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-1593791509702401/100000000000000)
    norm_num
  have hRef : reference 5 8 = (5987187/50000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_9 :
    (logLower 5 9 : ℝ) ≤ Real.log (reference 5 9 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (3352064403/200000000000000) (600613181/12807644431) (-10996497852281207/1000000000000000) 0 16 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 9 = (-10996497852281207/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (-373166600552711/100000000000000) + (-197807002917073/250000000000000) -
      (79311/50000000000) = (-10996497852281207/1000000000000000)
    norm_num
  have hRef : reference 5 9 = (3352064403/200000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_10 :
    (logLower 5 10 : ℝ) ≤ Real.log (reference 5 10 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (135920441841/200000000000000) (38264191841/233576691841) (-1823501125981451/250000000000000) 0 11 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 10 = (-1823501125981451/250000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (-135628182013/80000000000) + (874951606322501/1000000000000000) -
      (79311/50000000000) = (-1823501125981451/250000000000000)
    norm_num
  have hRef : reference 5 10 = (135920441841/200000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_11 :
    (logLower 5 11 : ℝ) ≤ Real.log (reference 5 11 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4916347649973/500000000000000) (1010097649973/8822597649973) (-4622043777378929/1000000000000000) 0 7 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 11 = (-4622043777378929/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (36721840469811/1000000000000000) + (362967643447413/200000000000000) -
      (79311/50000000000) = (-4622043777378929/1000000000000000)
    norm_num
  have hRef : reference 5 11 = (4916347649973/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_12 :
    (logLower 5 12 : ℝ) ≤ Real.log (reference 5 12 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (23181087001499/500000000000000) (7556087001499/38806087001499) (-3071272953889443/1000000000000000) 0 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 12 = (-3071272953889443/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (333091980134319/250000000000000) + (1034981480329543/500000000000000) -
      (79311/50000000000) = (-3071272953889443/1000000000000000)
    norm_num
  have hRef : reference 5 12 = (23181087001499/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_13 :
    (logLower 5 13 : ℝ) ≤ Real.log (reference 5 13 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (46270448827141/1000000000000000) (15020448827141/77520448827141) (-768313340538099/250000000000000) 0 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 13 = (-768313340538099/250000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (129538544282907/62500000000000) + (1327733764406897/1000000000000000) -
      (79311/50000000000) = (-768313340538099/250000000000000)
    norm_num
  have hRef : reference 5 13 = (46270448827141/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_14 :
    (logLower 5 14 : ℝ) ≤ Real.log (reference 5 14 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (1954993559307/200000000000000) (392493559307/3517493559307) (-925586410761259/200000000000000) 0 7 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 14 = (-925586410761259/200000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (906589587497413/500000000000000) + (8123151571171/250000000000000) -
      (79311/50000000000) = (-925586410761259/200000000000000)
    norm_num
  have hRef : reference 5 14 = (1954993559307/200000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_15 :
    (logLower 5 15 : ℝ) ≤ Real.log (reference 5 15 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (6732980627/10000000000000) (1850168127/11615793127) (-7303324025956123/1000000000000000) 0 11 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 15 = (-7303324025956123/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (865853967735169/1000000000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-7303324025956123/1000000000000000)
    norm_num
  have hRef : reference 5 15 = (6732980627/10000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_16 :
    (logLower 5 16 : ℝ) ≤ Real.log (reference 5 16 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (16665641441/1000000000000000) (2813704757/63848861007) (-11002162959137837/1000000000000000) 0 16 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 16 = (-11002162959137837/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1691812419889807/1000000000000000) +
      (-99424055919553/125000000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-11002162959137837/1000000000000000)
    norm_num
  have hRef : reference 5 16 = (16665641441/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_17 :
    (logLower 5 17 : ℝ) ≤ Real.log (reference 5 17 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (503272494557/1000000000000000) (14991244557/991553744557) (-30377521528351/4000000000000) 0 11 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 17 = (-30377521528351/4000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (44125432312857/1000000000000000) +
      (-373166600552711/100000000000000) + (874951606322501/1000000000000000) -
      (79311/50000000000) = (-30377521528351/4000000000000)
    norm_num
  have hRef : reference 5 17 = (503272494557/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_18 :
    (logLower 5 18 : ℝ) ≤ Real.log (reference 5 18 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4935379866239/500000000000000) (1029129866239/8841629866239) (-36079531568817/7812500000000) 0 7 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 18 = (-36079531568817/7812500000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (44125432312857/1000000000000000) +
      (-135628182013/80000000000) + (362967643447413/200000000000000) -
      (79311/50000000000) = (-36079531568817/7812500000000)
    norm_num
  have hRef : reference 5 18 = (4935379866239/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_19 :
    (logLower 5 19 : ℝ) ≤ Real.log (reference 5 19 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (36003944535563/500000000000000) (4753944535563/67253944535563) (-657745295438561/250000000000000) 0 4 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 19 = (-657745295438561/250000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (44125432312857/1000000000000000) +
      (36721840469811/1000000000000000) + (1034981480329543/500000000000000) -
      (79311/50000000000) = (-657745295438561/250000000000000)
    norm_num
  have hRef : reference 5 19 = (36003944535563/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_20 :
    (logLower 5 20 : ℝ) ≤ Real.log (reference 5 20 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (125235074508229/1000000000000000) (235074508229/250235074508229) (-259695537242371/125000000000000) 0 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 20 = (-259695537242371/125000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (44125432312857/1000000000000000) +
      (333091980134319/250000000000000) + (1327733764406897/1000000000000000) -
      (79311/50000000000) = (-259695537242371/125000000000000)
    norm_num
  have hRef : reference 5 20 = (125235074508229/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_21 :
    (logLower 5 21 : ℝ) ≤ Real.log (reference 5 21 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (71894530947661/1000000000000000) (9394530947661/134394530947661) (-526511333614389/200000000000000) 0 4 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 21 = (-526511333614389/200000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (44125432312857/1000000000000000) +
      (129538544282907/62500000000000) + (8123151571171/250000000000000) -
      (79311/50000000000) = (-526511333614389/200000000000000)
    norm_num
  have hRef : reference 5 21 = (71894530947661/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_22 :
    (logLower 5 22 : ℝ) ≤ Real.log (reference 5 22 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (9852211016811/1000000000000000) (2039711016811/17664711016811) (-2310030483246901/500000000000000) 0 7 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 22 = (-2310030483246901/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (44125432312857/1000000000000000) +
      (906589587497413/500000000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-2310030483246901/500000000000000)
    norm_num
  have hRef : reference 5 22 = (9852211016811/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_23 :
    (logLower 5 23 : ℝ) ≤ Real.log (reference 5 23 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (124491705503/250000000000000) (2421393003/246562018003) (-380248934592179/50000000000000) 0 11 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 23 = (-380248934592179/50000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (44125432312857/1000000000000000) +
      (865853967735169/1000000000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-380248934592179/50000000000000)
    norm_num
  have hRef : reference 5 23 = (124491705503/250000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_24 :
    (logLower 5 24 : ℝ) ≤ Real.log (reference 5 24 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4708494864347/1000000000000000) (802244864347/8614744864347) (-5358388569952367/1000000000000000) 0 8 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 24 = (-5358388569952367/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (335057658383419/250000000000000) +
      (-373166600552711/100000000000000) + (362967643447413/200000000000000) -
      (79311/50000000000) = (-5358388569952367/1000000000000000)
    norm_num
  have hRef : reference 5 24 = (4708494864347/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_25 :
    (logLower 5 25 : ℝ) ≤ Real.log (reference 5 25 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (46563024897117/1000000000000000) (15313024897117/77813024897117) (-383368762020717/125000000000000) 0 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 25 = (-383368762020717/125000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (335057658383419/250000000000000) +
      (-135628182013/80000000000) + (1034981480329543/500000000000000) -
      (79311/50000000000) = (-383368762020717/125000000000000)
    norm_num
  have hRef : reference 5 25 = (46563024897117/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_26 :
    (logLower 5 26 : ℝ) ≤ Real.log (reference 5 26 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (31323146445347/250000000000000) (73146445347/62573146445347) (-1038552588392807/500000000000000) 0 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 26 = (-1038552588392807/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (335057658383419/250000000000000) +
      (36721840469811/1000000000000000) + (1327733764406897/1000000000000000) -
      (79311/50000000000) = (-1038552588392807/500000000000000)
    norm_num
  have hRef : reference 5 26 = (31323146445347/250000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_27 :
    (logLower 5 27 : ℝ) ≤ Real.log (reference 5 27 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (12534332977193/100000000000000) (34332977193/25034332977193) (-1038350127420181/500000000000000) 0 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 27 = (-1038350127420181/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (335057658383419/250000000000000) +
      (333091980134319/250000000000000) + (8123151571171/250000000000000) -
      (79311/50000000000) = (-1038350127420181/500000000000000)
    norm_num
  have hRef : reference 5 27 = (12534332977193/100000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_28 :
    (logLower 5 28 : ℝ) ≤ Real.log (reference 5 28 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (23338198829289/500000000000000) (7713198829289/38963198829289) (-3064518231741297/1000000000000000) 0 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 28 = (-3064518231741297/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (335057658383419/250000000000000) +
      (129538544282907/62500000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-3064518231741297/1000000000000000)
    norm_num
  have hRef : reference 5 28 = (23338198829289/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_29 :
    (logLower 5 29 : ℝ) ≤ Real.log (reference 5 29 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4693640849553/1000000000000000) (787390849553/8599890849553) (-167548383855097/31250000000000) 0 8 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 29 = (-167548383855097/31250000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (335057658383419/250000000000000) +
      (906589587497413/500000000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-167548383855097/31250000000000)
    norm_num
  have hRef : reference 5 29 = (4693640849553/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_30 :
    (logLower 5 30 : ℝ) ≤ Real.log (reference 5 30 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (12700321560449/1000000000000000) (4887821560449/20512821560449) (-4366129552335803/1000000000000000) 0 7 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 30 = (-4366129552335803/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (2077364907728219/1000000000000000) +
      (-373166600552711/100000000000000) + (1034981480329543/500000000000000) -
      (79311/50000000000) = (-4366129552335803/1000000000000000)
    norm_num
  have hRef : reference 5 30 = (12700321560449/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_31 :
    (logLower 5 31 : ℝ) ≤ Real.log (reference 5 31 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4632639323631/100000000000000) (1507639323631/7757639323631) (-1536022509111691/500000000000000) 0 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 31 = (-1536022509111691/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (2077364907728219/1000000000000000) +
      (-135628182013/80000000000) + (1327733764406897/1000000000000000) -
      (79311/50000000000) = (-1536022509111691/500000000000000)
    norm_num
  have hRef : reference 5 31 = (4632639323631/100000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_32 :
    (logLower 5 32 : ℝ) ≤ Real.log (reference 5 32 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (71703875983153/1000000000000000) (9203875983153/134203875983153) (-658803015178321/250000000000000) 0 4 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 32 = (-658803015178321/250000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (2077364907728219/1000000000000000) +
      (36721840469811/1000000000000000) + (8123151571171/250000000000000) -
      (79311/50000000000) = (-658803015178321/250000000000000)
    norm_num
  have hRef : reference 5 32 = (71703875983153/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_33 :
    (logLower 5 33 : ℝ) ≤ Real.log (reference 5 33 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (46531249524447/1000000000000000) (15281249524447/77781249524447) (-306763274553599/100000000000000) 0 5 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 33 = (-306763274553599/100000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (2077364907728219/1000000000000000) +
      (333091980134319/250000000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-306763274553599/100000000000000)
    norm_num
  have hRef : reference 5 33 = (46531249524447/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_34 :
    (logLower 5 34 : ℝ) ≤ Real.log (reference 5 34 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (12714974451639/1000000000000000) (4902474451639/20527474451639) (-6983962361019/1600000000000) 0 7 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 34 = (-6983962361019/1600000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (2077364907728219/1000000000000000) +
      (129538544282907/62500000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-6983962361019/1600000000000)
    norm_num
  have hRef : reference 5 34 = (12714974451639/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_35 :
    (logLower 5 35 : ℝ) ≤ Real.log (reference 5 35 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4641382996567/1000000000000000) (735132996567/8547632996567) (-5372744483768123/1000000000000000) 0 8 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 35 = (-5372744483768123/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (226622396568511/125000000000000) +
      (-373166600552711/100000000000000) + (1327733764406897/1000000000000000) -
      (79311/50000000000) = (-5372744483768123/1000000000000000)
    norm_num
  have hRef : reference 5 35 = (4641382996567/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_36 :
    (logLower 5 36 : ℝ) ≤ Real.log (reference 5 36 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (4869239540797/500000000000000) (962989540797/8775489540797) (-2315835955762863/500000000000000) 0 7 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 36 = (-2315835955762863/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (226622396568511/125000000000000) +
      (-135628182013/80000000000) + (8123151571171/250000000000000) -
      (79311/50000000000) = (-2315835955762863/500000000000000)
    norm_num
  have hRef : reference 5 36 = (4869239540797/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_37 :
    (logLower 5 37 : ℝ) ≤ Real.log (reference 5 37 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (9777582881961/1000000000000000) (1965082881961/17590082881961) (-2313832280391793/500000000000000) 0 7 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 37 = (-2313832280391793/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (226622396568511/125000000000000) +
      (36721840469811/1000000000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-2313832280391793/500000000000000)
    norm_num
  have hRef : reference 5 37 = (9777582881961/1000000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_38 :
    (logLower 5 38 : ℝ) ≤ Real.log (reference 5 38 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (2327974755223/500000000000000) (374849755223/4281099755223) (-2684805499403121/500000000000000) 0 8 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 38 = (-2684805499403121/500000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (226622396568511/125000000000000) +
      (333091980134319/250000000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-2684805499403121/500000000000000)
    norm_num
  have hRef : reference 5 38 = (2327974755223/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_39 :
    (logLower 5 39 : ℝ) ≤ Real.log (reference 5 39 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (243888682727/500000000000000) (121818370227/365958995227) (-1906413265259907/250000000000000) 0 12 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 39 = (-1906413265259907/250000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (213827938349699/250000000000000) +
      (-373166600552711/100000000000000) + (8123151571171/250000000000000) -
      (79311/50000000000) = (-1906413265259907/250000000000000)
    norm_num
  have hRef : reference 5 39 = (243888682727/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_40 :
    (logLower 5 40 : ℝ) ≤ Real.log (reference 5 40 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (165970769903/250000000000000) (43900457403/288041082403) (-7317406095565189/1000000000000000) 0 11 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 40 = (-7317406095565189/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (213827938349699/250000000000000) +
      (-135628182013/80000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-7317406095565189/1000000000000000)
    norm_num
  have hRef : reference 5 40 = (165970769903/250000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_41 :
    (logLower 5 41 : ℝ) ≤ Real.log (reference 5 41 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (97822022803/200000000000000) (165772803/195478272803) (-7622924498022999/1000000000000000) 0 11 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 41 = (-7622924498022999/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (213827938349699/250000000000000) +
      (36721840469811/1000000000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-7622924498022999/1000000000000000)
    norm_num
  have hRef : reference 5 41 = (97822022803/200000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_42 :
    (logLower 5 42 : ℝ) ≤ Real.log (reference 5 42 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (8270750809/500000000000000) (2565425111/63600581361) (-11009639688052739/1000000000000000) 0 16 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 42 = (-11009639688052739/1000000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-50038006795259/62500000000000) +
      (-373166600552711/100000000000000) + (-1695574158605487/1000000000000000) -
      (79311/50000000000) = (-11009639688052739/1000000000000000)
    norm_num
  have hRef : reference 5 42 = (8270750809/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_43 :
    (logLower 5 43 : ℝ) ≤ Real.log (reference 5 43 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (206504523/12500000000000) (504629111/12711660361) (-44043673903113/4000000000000) 0 16 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 43 = (-44043673903113/4000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-50038006795259/62500000000000) +
      (-135628182013/80000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-44043673903113/4000000000000)
    norm_num
  have hRef : reference 5 43 = (206504523/12500000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem log_cert_44 :
    (logLower 5 44 : ℝ) ≤ Real.log (reference 5 44 : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
    (60421191/500000000000000) (418071667/61453227917) (-1592878049352127/100000000000000) 0 23 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ]) (by norm_num [sum_range_succ])
  have hLower : logLower 5 44 = (-1592878049352127/100000000000000 : ℚ) := by
    change (-2390894914487999/500000000000000 : ℚ) + (-1841078198051277/500000000000000) +
      (-373166600552711/100000000000000) + (-466645834586951/125000000000000) -
      (79311/50000000000) = (-1592878049352127/100000000000000)
    norm_num
  have hRef : reference 5 44 = (60421191/500000000000000 : ℚ) := rfl
  rw [hLower, hRef]
  exact h.1

private theorem all_logs (a : Fin 45) :
    (logLower 5 a : ℝ) ≤ Real.log (reference 5 a : ℝ) := by
  fin_cases a
  · exact log_cert_0
  · exact log_cert_1
  · exact log_cert_2
  · exact log_cert_3
  · exact log_cert_4
  · exact log_cert_5
  · exact log_cert_6
  · exact log_cert_7
  · exact log_cert_8
  · exact log_cert_9
  · exact log_cert_10
  · exact log_cert_11
  · exact log_cert_12
  · exact log_cert_13
  · exact log_cert_14
  · exact log_cert_15
  · exact log_cert_16
  · exact log_cert_17
  · exact log_cert_18
  · exact log_cert_19
  · exact log_cert_20
  · exact log_cert_21
  · exact log_cert_22
  · exact log_cert_23
  · exact log_cert_24
  · exact log_cert_25
  · exact log_cert_26
  · exact log_cert_27
  · exact log_cert_28
  · exact log_cert_29
  · exact log_cert_30
  · exact log_cert_31
  · exact log_cert_32
  · exact log_cert_33
  · exact log_cert_34
  · exact log_cert_35
  · exact log_cert_36
  · exact log_cert_37
  · exact log_cert_38
  · exact log_cert_39
  · exact log_cert_40
  · exact log_cert_41
  · exact log_cert_42
  · exact log_cert_43
  · exact log_cert_44

private theorem alpha_sum_rational : ∑ a, alpha 5 a = 1 := by decide +kernel
private theorem reference_sum_rational : ∑ a, reference 5 a = 1 := by decide +kernel
private theorem reference_pos_rational : ∀ a, 0 < reference 5 a := by decide +kernel
private theorem potential_bound_rational :
    -(∑ a, alpha 5 a * potential 5 a) + epsilon 5 ≤ entropyUpper 5 := by decide +kernel

theorem solution (rho : Fin 45 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 9),
      mme_modern_marginal (fun a ↦ coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ coarseAddress a mode)
        (fun a ↦ (alpha 5 a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ (entropyUpper 5 : ℝ) := by
  have hy : ∀ a, (0 : ℝ) < (reference 5 a : ℝ) := by
    intro a
    exact_mod_cast reference_pos_rational a
  have halphaSum : ∑ a, (alpha 5 a : ℝ) = 1 := by
    exact_mod_cast alpha_sum_rational
  have hySum : ∑ a, (reference 5 a : ℝ) = 1 := by
    exact_mod_cast reference_sum_rational
  have hlog : ∀ a,
      (lambdaZero 5 : ℝ) +
        (lambdaModes 5 0 (coarseAddress a 0) : ℝ) +
        (lambdaModes 5 1 (coarseAddress a 1) : ℝ) +
        (lambdaModes 5 2 (coarseAddress a 2) : ℝ) -
        (epsilon 5 : ℝ) ≤ Real.log (reference 5 a : ℝ) := by
    intro a
    have h := all_logs a
    simpa only [logLower, potential, Rat.cast_sub, Rat.cast_add] using h
  have h := mme_modern_entropyNat_upper_from_positive_reference
    (fun a ↦ coarseAddress a 0) (fun a ↦ coarseAddress a 1)
    (fun a ↦ coarseAddress a 2) rho
    (fun a ↦ (alpha 5 a : ℝ)) (fun a ↦ (reference 5 a : ℝ))
    (lambdaZero 5 : ℝ) (fun j ↦ (lambdaModes 5 0 j : ℝ))
    (fun j ↦ (lambdaModes 5 1 j : ℝ)) (fun j ↦ (lambdaModes 5 2 j : ℝ))
    (epsilon 5 : ℝ) hrho hy hrhoSum halphaSum hySum
    (hmarg 0) (hmarg 1) (hmarg 2) hlog
  have hbound : -(∑ a, (alpha 5 a : ℝ) * (potential 5 a : ℝ)) +
      (epsilon 5 : ℝ) ≤ (entropyUpper 5 : ℝ) := by
    exact_mod_cast potential_bound_rational
  apply h.trans
  simpa only [potential, Rat.cast_add] using hbound
