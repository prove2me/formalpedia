-- Prove2me | Definitions.Def_mme_dwz_fourth_exact_retained_entropy_arithmetic_data
-- name    : mme_dwz_fourth_exact_retained_entropy_arithmetic_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T19:00:19.208426+00:00
-- url     : https://prove2.me/theorems/2fc9db17-57a5-4524-9b9b-dfbafaa0dd4b
-- title:
--   Definitions for mme_dwz_fourth_exact_retained_entropy_arithmetic
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_exact_retained_entropy_arithmetic, from the exact fourth-power scalar assembly of Duan-Wu-Zhou.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_log_scale_table_data
import Theorems.Thm_mme_dwz_fourth_exact_log_scale_table
import Theorems.Thm_mme_entropy_interval_of_pointwise_log_interval

set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MME.DWZFourthRetainedEntropy

structure EntropyRecord where
  cells : List Nat
  lowerFloor : Rat
  upperCeiling : Rat

structure EntropyTerm where
  recordIndex : Nat
  useUpper : Bool
  coefficient : Rat

structure FloorBranch where
  retainedFloor : Rat
  constant : Rat
  terms : List EntropyTerm

def entropyRecords : Array EntropyRecord := #[
  {
    cells := [1220]
    lowerFloor := (321887580426641 / 1000000000000000 : Rat)
    upperCeiling := (160943791331333 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1732, 1705]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1644, 1793]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1793, 1644]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1746, 1691]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1732, 1705]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [662, 1920, 661]
    lowerFloor := (39421983917347 / 125000000000000 : Rat)
    upperCeiling := (315376177799673 / 1000000000000000 : Rat)
  },
  {
    cells := [661, 1920, 662]
    lowerFloor := (39421983917347 / 125000000000000 : Rat)
    upperCeiling := (315376177799673 / 1000000000000000 : Rat)
  },
  {
    cells := [663, 1919, 664]
    lowerFloor := (9855543798547 / 31250000000000 : Rat)
    upperCeiling := (315377708011079 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [664, 1919, 663]
    lowerFloor := (9855543798547 / 31250000000000 : Rat)
    upperCeiling := (315377708011079 / 1000000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1224, 1840, 1223]
    lowerFloor := (60559301455851 / 62500000000000 : Rat)
    upperCeiling := (968948837343163 / 1000000000000000 : Rat)
  },
  {
    cells := [1223, 1840, 1224]
    lowerFloor := (60559301455851 / 62500000000000 : Rat)
    upperCeiling := (968948837343163 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1732, 1705]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1746, 1691]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1644, 1793]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1793, 1644]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [626, 1530, 1529, 627]
    lowerFloor := (903280359845747 / 1000000000000000 : Rat)
    upperCeiling := (451640421002423 / 500000000000000 : Rat)
  },
  {
    cells := [627, 1529, 1530, 626]
    lowerFloor := (903280359845747 / 1000000000000000 : Rat)
    upperCeiling := (451640421002423 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [170, 972, 1865, 970, 171]
    lowerFloor := (394565704409721 / 500000000000000 : Rat)
    upperCeiling := (986414261817 / 1250000000000 : Rat)
  },
  {
    cells := [171, 970, 1865, 972, 170]
    lowerFloor := (394565704409721 / 500000000000000 : Rat)
    upperCeiling := (986414261817 / 1250000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [603, 1535, 1536, 602]
    lowerFloor := (436534250294129 / 500000000000000 : Rat)
    upperCeiling := (27283409188421 / 31250000000000 : Rat)
  },
  {
    cells := [602, 1536, 1535, 603]
    lowerFloor := (436534250294129 / 500000000000000 : Rat)
    upperCeiling := (27283409188421 / 31250000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1111, 1863, 1110]
    lowerFloor := (874682097185309 / 1000000000000000 : Rat)
    upperCeiling := (437341048621297 / 500000000000000 : Rat)
  },
  {
    cells := [1110, 1863, 1111]
    lowerFloor := (874682097185309 / 1000000000000000 : Rat)
    upperCeiling := (437341048621297 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1732, 1705]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1746, 1691]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1744, 1693]
    lowerFloor := (346573264158231 / 500000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [1692, 1745]
    lowerFloor := (43321658019779 / 62500000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [1387, 1528, 1386]
    lowerFloor := (1070229964333059 / 1000000000000000 : Rat)
    upperCeiling := (1070230040313821 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [3, 6, 1300, 1302, 2, 1301, 1303, 5, 7, 4]
    lowerFloor := (173298752497361 / 125000000000000 : Rat)
    upperCeiling := (1386391431102927 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1387, 1528, 1386]
    lowerFloor := (1070229964333059 / 1000000000000000 : Rat)
    upperCeiling := (1070230040313821 / 1000000000000000 : Rat)
  },
  {
    cells := [1330, 1331, 1328, 1329]
    lowerFloor := (173286713608307 / 125000000000000 : Rat)
    upperCeiling := (1386294414545107 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1322, 1332, 1327, 1337]
    lowerFloor := (173286713608309 / 125000000000000 : Rat)
    upperCeiling := (693147207272553 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [3, 6, 1300, 1302, 2, 1301, 1303, 5, 7, 4]
    lowerFloor := (173298752497361 / 125000000000000 : Rat)
    upperCeiling := (1386391431102927 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1387, 1528, 1386]
    lowerFloor := (1070229964333059 / 1000000000000000 : Rat)
    upperCeiling := (1070230040313821 / 1000000000000000 : Rat)
  },
  {
    cells := [1330, 1331, 1328, 1329]
    lowerFloor := (173286713608307 / 125000000000000 : Rat)
    upperCeiling := (1386294414545107 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1322, 1332, 1327, 1337]
    lowerFloor := (173286713608309 / 125000000000000 : Rat)
    upperCeiling := (693147207272553 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1739, 1698]
    lowerFloor := (86643316039557 / 125000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [1738, 1699]
    lowerFloor := (86643316039557 / 125000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [9, 1615, 1614, 8]
    lowerFloor := (173310017285663 / 250000000000000 : Rat)
    upperCeiling := (346620740125829 / 500000000000000 : Rat)
  },
  {
    cells := [1697, 1740]
    lowerFloor := (86643316039557 / 125000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [33, 1944, 32]
    lowerFloor := (50617539757 / 100000000000000 : Rat)
    upperCeiling := (126896384201 / 250000000000000 : Rat)
  },
  {
    cells := [32, 1610, 1608, 33]
    lowerFloor := (138724679945459 / 200000000000000 : Rat)
    upperCeiling := (693624809886529 / 1000000000000000 : Rat)
  },
  {
    cells := [34, 1943, 31]
    lowerFloor := (253091116809 / 500000000000000 : Rat)
    upperCeiling := (507592372837 / 1000000000000000 : Rat)
  },
  {
    cells := [1696, 1741]
    lowerFloor := (86643316039557 / 125000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [31, 1607, 1609, 34]
    lowerFloor := (693623406122251 / 1000000000000000 : Rat)
    upperCeiling := (173406204070367 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1496, 1211, 1497]
    lowerFloor := (525044736921653 / 500000000000000 : Rat)
    upperCeiling := (105008948593447 / 100000000000000 : Rat)
  },
  {
    cells := [1497, 1211, 1496]
    lowerFloor := (525044736921653 / 500000000000000 : Rat)
    upperCeiling := (105008948593447 / 100000000000000 : Rat)
  },
  {
    cells := [1823, 1612]
    lowerFloor := (693146527944441 / 1000000000000000 : Rat)
    upperCeiling := (693147233049507 / 1000000000000000 : Rat)
  },
  {
    cells := [1611, 1824]
    lowerFloor := (693146527942743 / 1000000000000000 : Rat)
    upperCeiling := (346573616523531 / 500000000000000 : Rat)
  },
  {
    cells := [71, 1938, 70]
    lowerFloor := (1763676483201 / 500000000000000 : Rat)
    upperCeiling := (3528754591937 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [669, 1916, 670]
    lowerFloor := (158222614968221 / 500000000000000 : Rat)
    upperCeiling := (158222767040777 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [670, 1916, 669]
    lowerFloor := (158222614968221 / 500000000000000 : Rat)
    upperCeiling := (158222767040777 / 500000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [870, 642, 643, 871, 854, 855, 646, 851, 644, 640, 641, 647, 852, 645, 868, 869]
    lowerFloor := (1308622483473077 / 500000000000000 : Rat)
    upperCeiling := (8178890719259 / 3125000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1497, 1211, 1496]
    lowerFloor := (525044736921653 / 500000000000000 : Rat)
    upperCeiling := (105008948593447 / 100000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [71, 1938, 70]
    lowerFloor := (1763676483201 / 500000000000000 : Rat)
    upperCeiling := (3528754591937 / 1000000000000000 : Rat)
  },
  {
    cells := [1314, 1315, 1344, 1345]
    lowerFloor := (1386293708871113 / 1000000000000000 : Rat)
    upperCeiling := (277258882908929 / 200000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1686, 1751]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [250, 1023, 249, 1092, 1093, 252, 1094, 1095, 1024, 251]
    lowerFloor := (378940894793829 / 200000000000000 : Rat)
    upperCeiling := (94735223707853 / 50000000000000 : Rat)
  },
  {
    cells := [670, 1916, 669]
    lowerFloor := (158222614968221 / 500000000000000 : Rat)
    upperCeiling := (158222767040777 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [71, 1938, 70]
    lowerFloor := (1763676483201 / 500000000000000 : Rat)
    upperCeiling := (3528754591937 / 1000000000000000 : Rat)
  },
  {
    cells := [870, 642, 643, 871, 854, 855, 646, 851, 644, 640, 641, 647, 852, 645, 868, 869]
    lowerFloor := (1308622483473077 / 500000000000000 : Rat)
    upperCeiling := (8178890719259 / 3125000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1497, 1211, 1496]
    lowerFloor := (525044736921653 / 500000000000000 : Rat)
    upperCeiling := (105008948593447 / 100000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [71, 1938, 70]
    lowerFloor := (1763676483201 / 500000000000000 : Rat)
    upperCeiling := (3528754591937 / 1000000000000000 : Rat)
  },
  {
    cells := [1314, 1315, 1344, 1345]
    lowerFloor := (1386293708871113 / 1000000000000000 : Rat)
    upperCeiling := (277258882908929 / 200000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1686, 1751]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [250, 1023, 249, 1092, 1093, 252, 1094, 1095, 1024, 251]
    lowerFloor := (378940894793829 / 200000000000000 : Rat)
    upperCeiling := (94735223707853 / 50000000000000 : Rat)
  },
  {
    cells := [670, 1916, 669]
    lowerFloor := (158222614968221 / 500000000000000 : Rat)
    upperCeiling := (158222767040777 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [71, 1938, 70]
    lowerFloor := (1763676483201 / 500000000000000 : Rat)
    upperCeiling := (3528754591937 / 1000000000000000 : Rat)
  },
  {
    cells := [1601, 1830]
    lowerFloor := (173286576904211 / 250000000000000 : Rat)
    upperCeiling := (346573502206009 / 500000000000000 : Rat)
  },
  {
    cells := [1468, 1450, 1467]
    lowerFloor := (274626511138587 / 250000000000000 : Rat)
    upperCeiling := (549253022309609 / 500000000000000 : Rat)
  },
  {
    cells := [1216, 1085, 998, 999, 1087, 1217]
    lowerFloor := (44579727083489 / 25000000000000 : Rat)
    upperCeiling := (222898635694973 / 125000000000000 : Rat)
  },
  {
    cells := [1196, 1842, 1197]
    lowerFloor := (232185153406429 / 250000000000000 : Rat)
    upperCeiling := (928740614728441 / 1000000000000000 : Rat)
  },
  {
    cells := [141, 1594, 1591, 142]
    lowerFloor := (44535981023949 / 62500000000000 : Rat)
    upperCeiling := (89072129352131 / 125000000000000 : Rat)
  },
  {
    cells := [142, 1404, 1192, 1191, 1405, 141]
    lowerFloor := (687216565318941 / 500000000000000 : Rat)
    upperCeiling := (5368879420047 / 3906250000000 : Rat)
  },
  {
    cells := [135, 1600, 1598, 136]
    lowerFloor := (35598067301187 / 50000000000000 : Rat)
    upperCeiling := (177990671771537 / 250000000000000 : Rat)
  },
  {
    cells := [1627, 1810]
    lowerFloor := (173286632080121 / 250000000000000 : Rat)
    upperCeiling := (693147233974717 / 1000000000000000 : Rat)
  },
  {
    cells := [136, 1463, 1081, 1080, 1464, 135]
    lowerFloor := (134138167986433 / 100000000000000 : Rat)
    upperCeiling := (83836354995897 / 62500000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [719, 1901, 718]
    lowerFloor := (383765001405687 / 1000000000000000 : Rat)
    upperCeiling := (383765183046681 / 1000000000000000 : Rat)
  },
  {
    cells := [718, 1901, 719]
    lowerFloor := (383765001405687 / 1000000000000000 : Rat)
    upperCeiling := (383765183046681 / 1000000000000000 : Rat)
  },
  {
    cells := [1736, 1701]
    lowerFloor := (693146528316453 / 1000000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1742, 1695]
    lowerFloor := (693146528316457 / 1000000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [128, 1932, 129]
    lowerFloor := (14246363667117 / 1000000000000000 : Rat)
    upperCeiling := (14247729247391 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [685, 1910, 686]
    lowerFloor := (163717792665677 / 500000000000000 : Rat)
    upperCeiling := (163717933179313 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [686, 1910, 685]
    lowerFloor := (163717792665677 / 500000000000000 : Rat)
    upperCeiling := (163717933179313 / 500000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [22, 510, 511, 54, 587, 56, 512, 513, 586, 1873, 588, 506, 508, 55, 589, 57, 507, 509, 23]
    lowerFloor := (1116805992044619 / 1000000000000000 : Rat)
    upperCeiling := (139600749357281 / 125000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [718, 1901, 719]
    lowerFloor := (383765001405687 / 1000000000000000 : Rat)
    upperCeiling := (383765183046681 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [128, 1932, 129]
    lowerFloor := (14246363667117 / 1000000000000000 : Rat)
    upperCeiling := (14247729247391 / 1000000000000000 : Rat)
  },
  {
    cells := [1294, 1295, 1362, 1363]
    lowerFloor := (1386281487686493 / 1000000000000000 : Rat)
    upperCeiling := (346570532661089 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1669, 1768]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [315, 316, 369, 1239, 370, 367, 371, 373, 1240, 374, 1241, 1242, 317, 368, 372, 318]
    lowerFloor := (1802029850552449 / 1000000000000000 : Rat)
    upperCeiling := (901015021592971 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [686, 1910, 685]
    lowerFloor := (163717792665677 / 500000000000000 : Rat)
    upperCeiling := (163717933179313 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [128, 1932, 129]
    lowerFloor := (14246363667117 / 1000000000000000 : Rat)
    upperCeiling := (14247729247391 / 1000000000000000 : Rat)
  },
  {
    cells := [22, 510, 511, 54, 587, 56, 512, 513, 586, 1873, 588, 506, 508, 55, 589, 57, 507, 509, 23]
    lowerFloor := (1116805992044619 / 1000000000000000 : Rat)
    upperCeiling := (139600749357281 / 125000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [718, 1901, 719]
    lowerFloor := (383765001405687 / 1000000000000000 : Rat)
    upperCeiling := (383765183046681 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [128, 1932, 129]
    lowerFloor := (14246363667117 / 1000000000000000 : Rat)
    upperCeiling := (14247729247391 / 1000000000000000 : Rat)
  },
  {
    cells := [1294, 1295, 1362, 1363]
    lowerFloor := (1386281487686493 / 1000000000000000 : Rat)
    upperCeiling := (346570532661089 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1669, 1768]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [315, 316, 369, 1239, 370, 367, 371, 373, 1240, 374, 1241, 1242, 317, 368, 372, 318]
    lowerFloor := (1802029850552449 / 1000000000000000 : Rat)
    upperCeiling := (901015021592971 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [686, 1910, 685]
    lowerFloor := (163717792665677 / 500000000000000 : Rat)
    upperCeiling := (163717933179313 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [128, 1932, 129]
    lowerFloor := (14246363667117 / 1000000000000000 : Rat)
    upperCeiling := (14247729247391 / 1000000000000000 : Rat)
  },
  {
    cells := [1642, 1795]
    lowerFloor := (346573264158317 / 500000000000000 : Rat)
    upperCeiling := (693147233975093 / 1000000000000000 : Rat)
  },
  {
    cells := [462, 1549, 1550, 463]
    lowerFloor := (816097029663039 / 1000000000000000 : Rat)
    upperCeiling := (408048937148503 / 500000000000000 : Rat)
  },
  {
    cells := [23, 756, 1523, 457, 456, 1522, 757, 22]
    lowerFloor := (29555985049751 / 25000000000000 : Rat)
    upperCeiling := (1182239548246039 / 1000000000000000 : Rat)
  },
  {
    cells := [1377, 1281, 1289, 1379]
    lowerFloor := (1385798739887003 / 1000000000000000 : Rat)
    upperCeiling := (1385799135012199 / 1000000000000000 : Rat)
  },
  {
    cells := [1012, 1278, 1280, 1265, 1011]
    lowerFloor := (396133534877029 / 250000000000000 : Rat)
    upperCeiling := (198066810755451 / 125000000000000 : Rat)
  },
  {
    cells := [1011, 951, 949, 922, 921, 950, 956, 1012]
    lowerFloor := (2074042606468169 / 1000000000000000 : Rat)
    upperCeiling := (2074043051186629 / 1000000000000000 : Rat)
  },
  {
    cells := [14, 777, 1887, 776, 15]
    lowerFloor := (125301486871947 / 250000000000000 : Rat)
    upperCeiling := (501206006166491 / 1000000000000000 : Rat)
  },
  {
    cells := [1641, 1796]
    lowerFloor := (693146528316641 / 1000000000000000 : Rat)
    upperCeiling := (173286808493773 / 250000000000000 : Rat)
  },
  {
    cells := [15, 742, 1526, 475, 474, 1527, 743, 14]
    lowerFloor := (9330997108179 / 8000000000000 : Rat)
    upperCeiling := (1166374719785649 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [694, 1906, 693]
    lowerFloor := (164952266296959 / 500000000000000 : Rat)
    upperCeiling := (329904808597719 / 1000000000000000 : Rat)
  },
  {
    cells := [693, 1906, 694]
    lowerFloor := (164952266296959 / 500000000000000 : Rat)
    upperCeiling := (329904808597719 / 1000000000000000 : Rat)
  },
  {
    cells := [1645, 1792]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1788, 1649]
    lowerFloor := (346573264158303 / 500000000000000 : Rat)
    upperCeiling := (138629446795019 / 200000000000000 : Rat)
  },
  {
    cells := [125, 1934, 124]
    lowerFloor := (13517480074819 / 1000000000000000 : Rat)
    upperCeiling := (1689856000159 / 125000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [723, 1899, 722]
    lowerFloor := (383849998349007 / 1000000000000000 : Rat)
    upperCeiling := (383850179865439 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [722, 1899, 723]
    lowerFloor := (383849998349007 / 1000000000000000 : Rat)
    upperCeiling := (383850179865439 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [259, 260, 356, 1261, 355, 352, 354, 358, 1262, 357, 1255, 1256, 261, 351, 353, 262]
    lowerFloor := (1792295073635629 / 1000000000000000 : Rat)
    upperCeiling := (1792295277514951 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [693, 1906, 694]
    lowerFloor := (164952266296959 / 500000000000000 : Rat)
    upperCeiling := (329904808597719 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [125, 1934, 124]
    lowerFloor := (13517480074819 / 1000000000000000 : Rat)
    upperCeiling := (1689856000159 / 125000000000000 : Rat)
  },
  {
    cells := [1306, 1307, 1352, 1353]
    lowerFloor := (1386293708880361 / 1000000000000000 : Rat)
    upperCeiling := (1386294414543191 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1664, 1773]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [84, 546, 547, 49, 571, 48, 548, 549, 573, 1866, 572, 550, 552, 47, 570, 46, 551, 553, 85]
    lowerFloor := (1158338998415653 / 1000000000000000 : Rat)
    upperCeiling := (579169500134351 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [722, 1899, 723]
    lowerFloor := (383849998349007 / 1000000000000000 : Rat)
    upperCeiling := (383850179865439 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [125, 1934, 124]
    lowerFloor := (13517480074819 / 1000000000000000 : Rat)
    upperCeiling := (1689856000159 / 125000000000000 : Rat)
  },
  {
    cells := [259, 260, 356, 1261, 355, 352, 354, 358, 1262, 357, 1255, 1256, 261, 351, 353, 262]
    lowerFloor := (1792295073635629 / 1000000000000000 : Rat)
    upperCeiling := (1792295277514951 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [693, 1906, 694]
    lowerFloor := (164952266296959 / 500000000000000 : Rat)
    upperCeiling := (329904808597719 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [125, 1934, 124]
    lowerFloor := (13517480074819 / 1000000000000000 : Rat)
    upperCeiling := (1689856000159 / 125000000000000 : Rat)
  },
  {
    cells := [1306, 1307, 1352, 1353]
    lowerFloor := (1386293708880361 / 1000000000000000 : Rat)
    upperCeiling := (1386294414543191 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1664, 1773]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [84, 546, 547, 49, 571, 48, 548, 549, 573, 1866, 572, 550, 552, 47, 570, 46, 551, 553, 85]
    lowerFloor := (1158338998415653 / 1000000000000000 : Rat)
    upperCeiling := (579169500134351 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [722, 1899, 723]
    lowerFloor := (383849998349007 / 1000000000000000 : Rat)
    upperCeiling := (383850179865439 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [125, 1934, 124]
    lowerFloor := (13517480074819 / 1000000000000000 : Rat)
    upperCeiling := (1689856000159 / 125000000000000 : Rat)
  },
  {
    cells := [1618, 1819]
    lowerFloor := (173286632085057 / 250000000000000 : Rat)
    upperCeiling := (693147233970687 / 1000000000000000 : Rat)
  },
  {
    cells := [100, 790, 1882, 791, 101]
    lowerFloor := (68901170714879 / 125000000000000 : Rat)
    upperCeiling := (17225293744771 / 31250000000000 : Rat)
  },
  {
    cells := [425, 1516, 775, 101, 100, 774, 1517, 424]
    lowerFloor := (1202623377515339 / 1000000000000000 : Rat)
    upperCeiling := (1202623411795383 / 1000000000000000 : Rat)
  },
  {
    cells := [754, 1208, 1831, 1209, 755]
    lowerFloor := (163613581782903 / 125000000000000 : Rat)
    upperCeiling := (261781738816821 / 200000000000000 : Rat)
  },
  {
    cells := [967, 1482, 1481, 968]
    lowerFloor := (126357890150619 / 100000000000000 : Rat)
    upperCeiling := (1263578902471541 / 1000000000000000 : Rat)
  },
  {
    cells := [781, 1360, 953, 755, 754, 952, 1361, 780]
    lowerFloor := (954385414185031 / 500000000000000 : Rat)
    upperCeiling := (1908771042184079 / 1000000000000000 : Rat)
  },
  {
    cells := [470, 1546, 1545, 471]
    lowerFloor := (408580198037837 / 500000000000000 : Rat)
    upperCeiling := (817161236189243 / 1000000000000000 : Rat)
  },
  {
    cells := [1617, 1820]
    lowerFloor := (346573264170387 / 500000000000000 : Rat)
    upperCeiling := (138629446794103 / 200000000000000 : Rat)
  },
  {
    cells := [441, 1504, 767, 85, 84, 766, 1505, 440]
    lowerFloor := (150941803192399 / 125000000000000 : Rat)
    upperCeiling := (1207534459542373 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [672, 1915, 671]
    lowerFloor := (79796444534257 / 250000000000000 : Rat)
    upperCeiling := (319186076401259 / 1000000000000000 : Rat)
  },
  {
    cells := [671, 1915, 672]
    lowerFloor := (79796444534257 / 250000000000000 : Rat)
    upperCeiling := (319186076401259 / 1000000000000000 : Rat)
  },
  {
    cells := [1816, 1621]
    lowerFloor := (346573264167063 / 500000000000000 : Rat)
    upperCeiling := (173286808493091 / 250000000000000 : Rat)
  },
  {
    cells := [1620, 1817]
    lowerFloor := (693146528334131 / 1000000000000000 : Rat)
    upperCeiling := (693147233972363 / 1000000000000000 : Rat)
  },
  {
    cells := [65, 1940, 64]
    lowerFloor := (909728685869 / 1000000000000000 : Rat)
    upperCeiling := (455568901359 / 500000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1501, 1206, 1500]
    lowerFloor := (1048182613146377 / 1000000000000000 : Rat)
    upperCeiling := (1048182625977613 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1500, 1206, 1501]
    lowerFloor := (1048182613146377 / 1000000000000000 : Rat)
    upperCeiling := (1048182625977613 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [288, 1114, 287, 1039, 1040, 290, 1041, 1042, 1115, 289]
    lowerFloor := (1902706454986929 / 1000000000000000 : Rat)
    upperCeiling := (951353228138681 / 500000000000000 : Rat)
  },
  {
    cells := [671, 1915, 672]
    lowerFloor := (79796444534257 / 250000000000000 : Rat)
    upperCeiling := (319186076401259 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [65, 1940, 64]
    lowerFloor := (909728685869 / 1000000000000000 : Rat)
    upperCeiling := (455568901359 / 500000000000000 : Rat)
  },
  {
    cells := [1354, 1355, 1304, 1305]
    lowerFloor := (173286713610849 / 125000000000000 : Rat)
    upperCeiling := (693147207270843 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1661, 1776]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [860, 616, 618, 861, 877, 878, 620, 858, 621, 617, 619, 622, 859, 623, 862, 863]
    lowerFloor := (324997429657631 / 125000000000000 : Rat)
    upperCeiling := (2599979458743839 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1500, 1206, 1501]
    lowerFloor := (1048182613146377 / 1000000000000000 : Rat)
    upperCeiling := (1048182625977613 / 1000000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [65, 1940, 64]
    lowerFloor := (909728685869 / 1000000000000000 : Rat)
    upperCeiling := (455568901359 / 500000000000000 : Rat)
  },
  {
    cells := [288, 1114, 287, 1039, 1040, 290, 1041, 1042, 1115, 289]
    lowerFloor := (1902706454986929 / 1000000000000000 : Rat)
    upperCeiling := (951353228138681 / 500000000000000 : Rat)
  },
  {
    cells := [671, 1915, 672]
    lowerFloor := (79796444534257 / 250000000000000 : Rat)
    upperCeiling := (319186076401259 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [65, 1940, 64]
    lowerFloor := (909728685869 / 1000000000000000 : Rat)
    upperCeiling := (455568901359 / 500000000000000 : Rat)
  },
  {
    cells := [1354, 1355, 1304, 1305]
    lowerFloor := (173286713610849 / 125000000000000 : Rat)
    upperCeiling := (693147207270843 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1661, 1776]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [860, 616, 618, 861, 877, 878, 620, 858, 621, 617, 619, 622, 859, 623, 862, 863]
    lowerFloor := (324997429657631 / 125000000000000 : Rat)
    upperCeiling := (2599979458743839 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1500, 1206, 1501]
    lowerFloor := (1048182613146377 / 1000000000000000 : Rat)
    upperCeiling := (1048182625977613 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [65, 1940, 64]
    lowerFloor := (909728685869 / 1000000000000000 : Rat)
    upperCeiling := (455568901359 / 500000000000000 : Rat)
  },
  {
    cells := [1818, 1619]
    lowerFloor := (693146528335911 / 1000000000000000 : Rat)
    upperCeiling := (693147233971919 / 1000000000000000 : Rat)
  },
  {
    cells := [322, 1587, 1586, 321]
    lowerFloor := (38323770572143 / 50000000000000 : Rat)
    upperCeiling := (766476496789097 / 1000000000000000 : Rat)
  },
  {
    cells := [1139, 1424, 321, 322, 1425, 1136]
    lowerFloor := (1408645438958251 / 1000000000000000 : Rat)
    upperCeiling := (1408645441138519 / 1000000000000000 : Rat)
  },
  {
    cells := [332, 1579, 1574, 330]
    lowerFloor := (192271687108539 / 250000000000000 : Rat)
    upperCeiling := (384543912084939 / 500000000000000 : Rat)
  },
  {
    cells := [1159, 1857, 1160]
    lowerFloor := (90913756859429 / 100000000000000 : Rat)
    upperCeiling := (227284392221657 / 250000000000000 : Rat)
  },
  {
    cells := [1131, 1428, 330, 332, 1429, 1130]
    lowerFloor := (141044080932503 / 100000000000000 : Rat)
    upperCeiling := (1410440814732057 / 1000000000000000 : Rat)
  },
  {
    cells := [1452, 1478, 1449]
    lowerFloor := (549099892604583 / 500000000000000 : Rat)
    upperCeiling := (1098199785293293 / 1000000000000000 : Rat)
  },
  {
    cells := [1590, 1832]
    lowerFloor := (2707353479819 / 3906250000000 : Rat)
    upperCeiling := (693083060250497 / 1000000000000000 : Rat)
  },
  {
    cells := [986, 1091, 1213, 1212, 1150, 987]
    lowerFloor := (444956033493823 / 250000000000000 : Rat)
    upperCeiling := (1779824135844573 / 1000000000000000 : Rat)
  },
  {
    cells := [1606, 1825]
    lowerFloor := (86643315896289 / 125000000000000 : Rat)
    upperCeiling := (173286808004591 / 250000000000000 : Rat)
  },
  {
    cells := [1828, 1603]
    lowerFloor := (173286631772569 / 250000000000000 : Rat)
    upperCeiling := (13862944638347 / 20000000000000 : Rat)
  },
  {
    cells := [600, 1921, 601]
    lowerFloor := (51459939683169 / 250000000000000 : Rat)
    upperCeiling := (102920183466507 / 500000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1312, 1313, 1346, 1347]
    lowerFloor := (1386293708872287 / 1000000000000000 : Rat)
    upperCeiling := (693147207272251 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1339, 1341, 1318, 1320]
    lowerFloor := (693146854433279 / 500000000000000 : Rat)
    upperCeiling := (1386294414545099 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [178, 932, 1202, 1203, 180, 1204, 1205, 179, 933, 181]
    lowerFloor := (227353427208299 / 125000000000000 : Rat)
    upperCeiling := (227353434082969 / 125000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [600, 1921, 601]
    lowerFloor := (51459939683169 / 250000000000000 : Rat)
    upperCeiling := (102920183466507 / 500000000000000 : Rat)
  },
  {
    cells := [1312, 1313, 1346, 1347]
    lowerFloor := (1386293708872287 / 1000000000000000 : Rat)
    upperCeiling := (693147207272251 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1339, 1341, 1318, 1320]
    lowerFloor := (693146854433279 / 500000000000000 : Rat)
    upperCeiling := (1386294414545099 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [178, 932, 1202, 1203, 180, 1204, 1205, 179, 933, 181]
    lowerFloor := (227353427208299 / 125000000000000 : Rat)
    upperCeiling := (227353434082969 / 125000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [600, 1921, 601]
    lowerFloor := (51459939683169 / 250000000000000 : Rat)
    upperCeiling := (102920183466507 / 500000000000000 : Rat)
  },
  {
    cells := [1808, 1629]
    lowerFloor := (86643316039889 / 125000000000000 : Rat)
    upperCeiling := (43321702123429 / 62500000000000 : Rat)
  },
  {
    cells := [941, 1871, 940]
    lowerFloor := (356521592069023 / 500000000000000 : Rat)
    upperCeiling := (713043317975361 / 1000000000000000 : Rat)
  },
  {
    cells := [1491, 940, 941, 1488]
    lowerFloor := (620739254754353 / 500000000000000 : Rat)
    upperCeiling := (124147864336127 / 100000000000000 : Rat)
  },
  {
    cells := [1375, 1540, 1376]
    lowerFloor := (524874171690303 / 500000000000000 : Rat)
    upperCeiling := (524874367812923 / 500000000000000 : Rat)
  },
  {
    cells := [1785, 1652]
    lowerFloor := (86643316039569 / 125000000000000 : Rat)
    upperCeiling := (693147233975099 / 1000000000000000 : Rat)
  },
  {
    cells := [1284, 1376, 1375, 1283]
    lowerFloor := (1385836236355013 / 1000000000000000 : Rat)
    upperCeiling := (43307394644061 / 31250000000000 : Rat)
  },
  {
    cells := [1706, 1731]
    lowerFloor := (693146528316451 / 1000000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1733, 1704]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1490, 939, 938, 1489]
    lowerFloor := (620739156044381 / 500000000000000 : Rat)
    upperCeiling := (1241478445939443 / 1000000000000000 : Rat)
  },
  {
    cells := [1644, 1793]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1793, 1644]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1222, 1841, 1221]
    lowerFloor := (242237204168137 / 250000000000000 : Rat)
    upperCeiling := (968948830722089 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1221, 1841, 1222]
    lowerFloor := (242237204168137 / 250000000000000 : Rat)
    upperCeiling := (968948830722089 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [667, 1917, 668]
    lowerFloor := (316445225615747 / 1000000000000000 : Rat)
    upperCeiling := (79111382440217 / 250000000000000 : Rat)
  },
  {
    cells := [668, 1917, 667]
    lowerFloor := (316445225615747 / 1000000000000000 : Rat)
    upperCeiling := (79111382440217 / 250000000000000 : Rat)
  },
  {
    cells := [1605, 1826]
    lowerFloor := (346573263547781 / 500000000000000 : Rat)
    upperCeiling := (346573615962001 / 500000000000000 : Rat)
  },
  {
    cells := [1827, 1604]
    lowerFloor := (346573263546787 / 500000000000000 : Rat)
    upperCeiling := (1386294463843 / 2000000000000 : Rat)
  },
  {
    cells := [72, 1937, 73]
    lowerFloor := (3766860043419 / 1000000000000000 : Rat)
    upperCeiling := (1884130471091 / 500000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1498, 1210, 1499]
    lowerFloor := (1049980405834763 / 1000000000000000 : Rat)
    upperCeiling := (209996083592751 / 200000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1499, 1210, 1498]
    lowerFloor := (1049980405834763 / 1000000000000000 : Rat)
    upperCeiling := (209996083592751 / 200000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [872, 636, 637, 873, 849, 850, 648, 847, 650, 638, 639, 649, 848, 651, 874, 875]
    lowerFloor := (2617150833681507 / 1000000000000000 : Rat)
    upperCeiling := (52343017933231 / 20000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1499, 1210, 1498]
    lowerFloor := (1049980405834763 / 1000000000000000 : Rat)
    upperCeiling := (209996083592751 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [72, 1937, 73]
    lowerFloor := (3766860043419 / 1000000000000000 : Rat)
    upperCeiling := (1884130471091 / 500000000000000 : Rat)
  },
  {
    cells := [245, 1021, 246, 1096, 1097, 247, 1098, 1099, 1022, 248]
    lowerFloor := (473675747147097 / 250000000000000 : Rat)
    upperCeiling := (189470298877627 / 100000000000000 : Rat)
  },
  {
    cells := [668, 1917, 667]
    lowerFloor := (316445225615747 / 1000000000000000 : Rat)
    upperCeiling := (79111382440217 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [72, 1937, 73]
    lowerFloor := (3766860043419 / 1000000000000000 : Rat)
    upperCeiling := (1884130471091 / 500000000000000 : Rat)
  },
  {
    cells := [1316, 1317, 1342, 1343]
    lowerFloor := (1386293708870253 / 1000000000000000 : Rat)
    upperCeiling := (1386294414544743 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1659, 1778]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [872, 636, 637, 873, 849, 850, 648, 847, 650, 638, 639, 649, 848, 651, 874, 875]
    lowerFloor := (2617150833681507 / 1000000000000000 : Rat)
    upperCeiling := (52343017933231 / 20000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1499, 1210, 1498]
    lowerFloor := (1049980405834763 / 1000000000000000 : Rat)
    upperCeiling := (209996083592751 / 200000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [72, 1937, 73]
    lowerFloor := (3766860043419 / 1000000000000000 : Rat)
    upperCeiling := (1884130471091 / 500000000000000 : Rat)
  },
  {
    cells := [245, 1021, 246, 1096, 1097, 247, 1098, 1099, 1022, 248]
    lowerFloor := (473675747147097 / 250000000000000 : Rat)
    upperCeiling := (189470298877627 / 100000000000000 : Rat)
  },
  {
    cells := [668, 1917, 667]
    lowerFloor := (316445225615747 / 1000000000000000 : Rat)
    upperCeiling := (79111382440217 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [72, 1937, 73]
    lowerFloor := (3766860043419 / 1000000000000000 : Rat)
    upperCeiling := (1884130471091 / 500000000000000 : Rat)
  },
  {
    cells := [1316, 1317, 1342, 1343]
    lowerFloor := (1386293708870253 / 1000000000000000 : Rat)
    upperCeiling := (1386294414544743 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1659, 1778]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1471, 1447, 1469]
    lowerFloor := (1098480054569779 / 1000000000000000 : Rat)
    upperCeiling := (1098480054635537 / 1000000000000000 : Rat)
  },
  {
    cells := [1602, 1829]
    lowerFloor := (138629289626349 / 200000000000000 : Rat)
    upperCeiling := (346573574185711 / 500000000000000 : Rat)
  },
  {
    cells := [1219, 1000, 1082, 1086, 997, 1218]
    lowerFloor := (13929716725763 / 7812500000000 : Rat)
    upperCeiling := (111437733954581 / 62500000000000 : Rat)
  },
  {
    cells := [1628, 1809]
    lowerFloor := (346573264159833 / 500000000000000 : Rat)
    upperCeiling := (693147233974807 / 1000000000000000 : Rat)
  },
  {
    cells := [137, 1599, 1597, 138]
    lowerFloor := (142392695807913 / 200000000000000 : Rat)
    upperCeiling := (355982410046433 / 500000000000000 : Rat)
  },
  {
    cells := [138, 1078, 1465, 1466, 1079, 137]
    lowerFloor := (134137991574853 / 100000000000000 : Rat)
    upperCeiling := (1341379915818559 / 1000000000000000 : Rat)
  },
  {
    cells := [143, 1593, 1592, 144]
    lowerFloor := (712576301553461 / 1000000000000000 : Rat)
    upperCeiling := (71257763998473 / 100000000000000 : Rat)
  },
  {
    cells := [1194, 1843, 1195]
    lowerFloor := (928738227798501 / 1000000000000000 : Rat)
    upperCeiling := (928738228901049 / 1000000000000000 : Rat)
  },
  {
    cells := [144, 1189, 1406, 1407, 1190, 143]
    lowerFloor := (687216319293413 / 500000000000000 : Rat)
    upperCeiling := (343608159870207 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [708, 1905, 707]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [707, 1905, 708]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [1789, 1648]
    lowerFloor := (10830414504947 / 15625000000000 : Rat)
    upperCeiling := (138629446795019 / 200000000000000 : Rat)
  },
  {
    cells := [1790, 1647]
    lowerFloor := (69314652831661 / 100000000000000 : Rat)
    upperCeiling := (138629446795019 / 200000000000000 : Rat)
  },
  {
    cells := [215, 1928, 216]
    lowerFloor := (684733503167 / 10000000000000 : Rat)
    upperCeiling := (6847449503161 / 100000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [736, 1893, 737]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [737, 1893, 736]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [20, 502, 503, 119, 492, 117, 504, 505, 493, 1877, 495, 498, 500, 118, 494, 116, 499, 501, 21]
    lowerFloor := (1062374076161437 / 1000000000000000 : Rat)
    upperCeiling := (265593520404217 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [707, 1905, 708]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [737, 1893, 736]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1672, 1765]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [215, 1928, 216]
    lowerFloor := (684733503167 / 10000000000000 : Rat)
    upperCeiling := (6847449503161 / 100000000000000 : Rat)
  },
  {
    cells := [279, 1100, 281, 1047, 1048, 280, 1049, 1050, 1101, 282]
    lowerFloor := (1901820476122637 / 1000000000000000 : Rat)
    upperCeiling := (950910238544083 / 500000000000000 : Rat)
  },
  {
    cells := [707, 1905, 708]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [737, 1893, 736]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1683, 1754]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [215, 1928, 216]
    lowerFloor := (684733503167 / 10000000000000 : Rat)
    upperCeiling := (6847449503161 / 100000000000000 : Rat)
  },
  {
    cells := [417, 1416, 416, 804, 806, 415, 805, 807, 1417, 414]
    lowerFloor := (1745990204911181 / 1000000000000000 : Rat)
    upperCeiling := (872995102524459 / 500000000000000 : Rat)
  },
  {
    cells := [707, 1905, 708]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [737, 1893, 736]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1677, 1760]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [215, 1928, 216]
    lowerFloor := (684733503167 / 10000000000000 : Rat)
    upperCeiling := (6847449503161 / 100000000000000 : Rat)
  },
  {
    cells := [20, 502, 503, 119, 492, 117, 504, 505, 493, 1877, 495, 498, 500, 118, 494, 116, 499, 501, 21]
    lowerFloor := (1062374076161437 / 1000000000000000 : Rat)
    upperCeiling := (265593520404217 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [737, 1893, 736]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [707, 1905, 708]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1672, 1765]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [215, 1928, 216]
    lowerFloor := (684733503167 / 10000000000000 : Rat)
    upperCeiling := (6847449503161 / 100000000000000 : Rat)
  },
  {
    cells := [279, 1100, 281, 1047, 1048, 280, 1049, 1050, 1101, 282]
    lowerFloor := (1901820476122637 / 1000000000000000 : Rat)
    upperCeiling := (950910238544083 / 500000000000000 : Rat)
  },
  {
    cells := [737, 1893, 736]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [707, 1905, 708]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1683, 1754]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [215, 1928, 216]
    lowerFloor := (684733503167 / 10000000000000 : Rat)
    upperCeiling := (6847449503161 / 100000000000000 : Rat)
  },
  {
    cells := [417, 1416, 416, 804, 806, 415, 805, 807, 1417, 414]
    lowerFloor := (1745990204911181 / 1000000000000000 : Rat)
    upperCeiling := (872995102524459 / 500000000000000 : Rat)
  },
  {
    cells := [737, 1893, 736]
    lowerFloor := (423916469321411 / 1000000000000000 : Rat)
    upperCeiling := (423916610606277 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [707, 1905, 708]
    lowerFloor := (11064048008917 / 31250000000000 : Rat)
    upperCeiling := (22128110398861 / 62500000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1677, 1760]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [215, 1928, 216]
    lowerFloor := (684733503167 / 10000000000000 : Rat)
    upperCeiling := (6847449503161 / 100000000000000 : Rat)
  },
  {
    cells := [1171, 1851, 1170]
    lowerFloor := (455489518199093 / 500000000000000 : Rat)
    upperCeiling := (1423404744889 / 1562500000000 : Rat)
  },
  {
    cells := [1169, 1852, 1172]
    lowerFloor := (910979021760953 / 1000000000000000 : Rat)
    upperCeiling := (910979022091727 / 1000000000000000 : Rat)
  },
  {
    cells := [21, 656, 1014, 655, 1838, 657, 1013, 658, 20]
    lowerFloor := (54900396948451 / 40000000000000 : Rat)
    upperCeiling := (686254961877371 / 500000000000000 : Rat)
  },
  {
    cells := [1181, 1846, 1182]
    lowerFloor := (911453159561059 / 1000000000000000 : Rat)
    upperCeiling := (911453159902569 / 1000000000000000 : Rat)
  },
  {
    cells := [10, 783, 1885, 782, 11]
    lowerFloor := (254444759944667 / 500000000000000 : Rat)
    upperCeiling := (127222393437081 / 250000000000000 : Rat)
  },
  {
    cells := [11, 653, 1015, 659, 1839, 660, 1016, 654, 10]
    lowerFloor := (340453451669857 / 250000000000000 : Rat)
    upperCeiling := (1361813806762189 / 1000000000000000 : Rat)
  },
  {
    cells := [993, 1232, 1397, 1231, 994]
    lowerFloor := (156758079554891 / 100000000000000 : Rat)
    upperCeiling := (1567580832291859 / 1000000000000000 : Rat)
  },
  {
    cells := [1474, 1443, 1475]
    lowerFloor := (109824337772429 / 100000000000000 : Rat)
    upperCeiling := (274560844449463 / 250000000000000 : Rat)
  },
  {
    cells := [994, 907, 839, 903, 881, 908, 843, 904, 993]
    lowerFloor := (2188319386552521 / 1000000000000000 : Rat)
    upperCeiling := (1068515345013 / 488281250000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [730, 1896, 731]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [731, 1896, 730]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [1639, 1798]
    lowerFloor := (693146528317001 / 1000000000000000 : Rat)
    upperCeiling := (346573616987531 / 500000000000000 : Rat)
  },
  {
    cells := [1640, 1797]
    lowerFloor := (693146528317001 / 1000000000000000 : Rat)
    upperCeiling := (346573616987531 / 500000000000000 : Rat)
  },
  {
    cells := [254, 1925, 253]
    lowerFloor := (73973800365523 / 1000000000000000 : Rat)
    upperCeiling := (73974921821109 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [749, 1890, 748]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [748, 1890, 749]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [301, 302, 213, 1276, 209, 211, 212, 214, 1277, 210, 1274, 1275, 299, 207, 208, 300]
    lowerFloor := (1718326045928399 / 1000000000000000 : Rat)
    upperCeiling := (1718326379666223 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [731, 1896, 730]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [748, 1890, 749]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1682, 1755]
    lowerFloor := (27725861132659 / 40000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [254, 1925, 253]
    lowerFloor := (73973800365523 / 1000000000000000 : Rat)
    upperCeiling := (73974921821109 / 1000000000000000 : Rat)
  },
  {
    cells := [167, 1146, 166, 1065, 1066, 169, 1067, 1068, 1147, 168]
    lowerFloor := (1837823390555649 / 1000000000000000 : Rat)
    upperCeiling := (1837823390689161 / 1000000000000000 : Rat)
  },
  {
    cells := [731, 1896, 730]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [748, 1890, 749]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1673, 1764]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [254, 1925, 253]
    lowerFloor := (73973800365523 / 1000000000000000 : Rat)
    upperCeiling := (73974921821109 / 1000000000000000 : Rat)
  },
  {
    cells := [899, 900, 227, 981, 225, 219, 220, 228, 982, 226, 974, 975, 897, 217, 218, 898]
    lowerFloor := (2260445594391519 / 1000000000000000 : Rat)
    upperCeiling := (452089124266071 / 200000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [731, 1896, 730]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [748, 1890, 749]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1679, 1758]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [254, 1925, 253]
    lowerFloor := (73973800365523 / 1000000000000000 : Rat)
    upperCeiling := (73974921821109 / 1000000000000000 : Rat)
  },
  {
    cells := [301, 302, 213, 1276, 209, 211, 212, 214, 1277, 210, 1274, 1275, 299, 207, 208, 300]
    lowerFloor := (1718326045928399 / 1000000000000000 : Rat)
    upperCeiling := (1718326379666223 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [748, 1890, 749]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [731, 1896, 730]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1682, 1755]
    lowerFloor := (27725861132659 / 40000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [254, 1925, 253]
    lowerFloor := (73973800365523 / 1000000000000000 : Rat)
    upperCeiling := (73974921821109 / 1000000000000000 : Rat)
  },
  {
    cells := [167, 1146, 166, 1065, 1066, 169, 1067, 1068, 1147, 168]
    lowerFloor := (1837823390555649 / 1000000000000000 : Rat)
    upperCeiling := (1837823390689161 / 1000000000000000 : Rat)
  },
  {
    cells := [748, 1890, 749]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [731, 1896, 730]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1673, 1764]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [254, 1925, 253]
    lowerFloor := (73973800365523 / 1000000000000000 : Rat)
    upperCeiling := (73974921821109 / 1000000000000000 : Rat)
  },
  {
    cells := [899, 900, 227, 981, 225, 219, 220, 228, 982, 226, 974, 975, 897, 217, 218, 898]
    lowerFloor := (2260445594391519 / 1000000000000000 : Rat)
    upperCeiling := (452089124266071 / 200000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [748, 1890, 749]
    lowerFloor := (217049532506361 / 500000000000000 : Rat)
    upperCeiling := (217049604725953 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [731, 1896, 730]
    lowerFloor := (410822095985171 / 1000000000000000 : Rat)
    upperCeiling := (41082224451561 / 100000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1679, 1758]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [254, 1925, 253]
    lowerFloor := (73973800365523 / 1000000000000000 : Rat)
    upperCeiling := (73974921821109 / 1000000000000000 : Rat)
  },
  {
    cells := [1163, 1855, 1164]
    lowerFloor := (28420206614313 / 31250000000000 : Rat)
    upperCeiling := (454723305978229 / 500000000000000 : Rat)
  },
  {
    cells := [444, 1563, 1564, 445]
    lowerFloor := (50959501007927 / 62500000000000 : Rat)
    upperCeiling := (815352863993599 / 1000000000000000 : Rat)
  },
  {
    cells := [394, 1061, 397, 148, 1414, 1415, 149, 395, 1062, 396]
    lowerFloor := (1541113807368923 / 1000000000000000 : Rat)
    upperCeiling := (770556903830077 / 500000000000000 : Rat)
  },
  {
    cells := [448, 1559, 1560, 449]
    lowerFloor := (20394693594651 / 25000000000000 : Rat)
    upperCeiling := (815788589756039 / 1000000000000000 : Rat)
  },
  {
    cells := [433, 1572, 1571, 432]
    lowerFloor := (814084444455973 / 1000000000000000 : Rat)
    upperCeiling := (32563411917049 / 40000000000000 : Rat)
  },
  {
    cells := [386, 1029, 401, 152, 1436, 1437, 153, 400, 1030, 387]
    lowerFloor := (38442870494907 / 25000000000000 : Rat)
    upperCeiling := (1537714820160819 / 1000000000000000 : Rat)
  },
  {
    cells := [1229, 1392, 1391, 1230]
    lowerFloor := (688017809983191 / 500000000000000 : Rat)
    upperCeiling := (688017823328271 / 500000000000000 : Rat)
  },
  {
    cells := [1400, 1492, 1403]
    lowerFloor := (1091510545917621 / 1000000000000000 : Rat)
    upperCeiling := (109151054814571 / 100000000000000 : Rat)
  },
  {
    cells := [889, 837, 892, 906, 823, 822, 905, 890, 846, 891]
    lowerFloor := (229888748449311 / 100000000000000 : Rat)
    upperCeiling := (2298887522461779 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [739, 1892, 738]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [738, 1892, 739]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [1702, 1735]
    lowerFloor := (693146528316453 / 1000000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1707, 1730]
    lowerFloor := (693146528316451 / 1000000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [190, 1929, 189]
    lowerFloor := (6800924900301 / 100000000000000 : Rat)
    upperCeiling := (68010395683741 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [712, 1903, 711]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [711, 1903, 712]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [406, 1409, 407, 808, 809, 408, 810, 811, 1408, 409]
    lowerFloor := (13662979162683 / 7812500000000 : Rat)
    upperCeiling := (1748861332944749 / 1000000000000000 : Rat)
  },
  {
    cells := [738, 1892, 739]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [711, 1903, 712]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1667, 1770]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [190, 1929, 189]
    lowerFloor := (6800924900301 / 100000000000000 : Rat)
    upperCeiling := (68010395683741 / 1000000000000000 : Rat)
  },
  {
    cells := [275, 1102, 276, 1057, 1059, 277, 1058, 1060, 1103, 278]
    lowerFloor := (950296050636709 / 500000000000000 : Rat)
    upperCeiling := (380118420391359 / 200000000000000 : Rat)
  },
  {
    cells := [738, 1892, 739]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [711, 1903, 712]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1663, 1774]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [190, 1929, 189]
    lowerFloor := (6800924900301 / 100000000000000 : Rat)
    upperCeiling := (68010395683741 / 1000000000000000 : Rat)
  },
  {
    cells := [92, 562, 563, 108, 491, 109, 564, 565, 489, 1874, 488, 566, 568, 110, 490, 111, 567, 569, 93]
    lowerFloor := (280108210895703 / 250000000000000 : Rat)
    upperCeiling := (280108211672089 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [738, 1892, 739]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [711, 1903, 712]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1671, 1766]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [190, 1929, 189]
    lowerFloor := (6800924900301 / 100000000000000 : Rat)
    upperCeiling := (68010395683741 / 1000000000000000 : Rat)
  },
  {
    cells := [406, 1409, 407, 808, 809, 408, 810, 811, 1408, 409]
    lowerFloor := (13662979162683 / 7812500000000 : Rat)
    upperCeiling := (1748861332944749 / 1000000000000000 : Rat)
  },
  {
    cells := [711, 1903, 712]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [738, 1892, 739]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1667, 1770]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [190, 1929, 189]
    lowerFloor := (6800924900301 / 100000000000000 : Rat)
    upperCeiling := (68010395683741 / 1000000000000000 : Rat)
  },
  {
    cells := [275, 1102, 276, 1057, 1059, 277, 1058, 1060, 1103, 278]
    lowerFloor := (950296050636709 / 500000000000000 : Rat)
    upperCeiling := (380118420391359 / 200000000000000 : Rat)
  },
  {
    cells := [711, 1903, 712]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [738, 1892, 739]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1663, 1774]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [190, 1929, 189]
    lowerFloor := (6800924900301 / 100000000000000 : Rat)
    upperCeiling := (68010395683741 / 1000000000000000 : Rat)
  },
  {
    cells := [92, 562, 563, 108, 491, 109, 564, 565, 489, 1874, 488, 566, 568, 110, 490, 111, 567, 569, 93]
    lowerFloor := (280108210895703 / 250000000000000 : Rat)
    upperCeiling := (280108211672089 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [711, 1903, 712]
    lowerFloor := (35637939895643 / 100000000000000 : Rat)
    upperCeiling := (178189812464087 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [738, 1892, 739]
    lowerFloor := (424238948620651 / 1000000000000000 : Rat)
    upperCeiling := (424239089859847 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1671, 1766]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [190, 1929, 189]
    lowerFloor := (6800924900301 / 100000000000000 : Rat)
    upperCeiling := (68010395683741 / 1000000000000000 : Rat)
  },
  {
    cells := [1472, 1446, 1473]
    lowerFloor := (549202205644569 / 500000000000000 : Rat)
    upperCeiling := (43936176454297 / 40000000000000 : Rat)
  },
  {
    cells := [990, 1235, 1394, 1236, 991]
    lowerFloor := (391788957119819 / 250000000000000 : Rat)
    upperCeiling := (783577939197407 / 500000000000000 : Rat)
  },
  {
    cells := [836, 915, 991, 913, 882, 914, 990, 916, 835]
    lowerFloor := (1094210538314229 / 500000000000000 : Rat)
    upperCeiling := (1094210564878637 / 500000000000000 : Rat)
  },
  {
    cells := [86, 796, 1879, 797, 87]
    lowerFloor := (553194897997683 / 1000000000000000 : Rat)
    upperCeiling := (553194931183759 / 1000000000000000 : Rat)
  },
  {
    cells := [1186, 1844, 1185]
    lowerFloor := (911729073072331 / 1000000000000000 : Rat)
    upperCeiling := (911729073420257 / 1000000000000000 : Rat)
  },
  {
    cells := [1007, 680, 87, 705, 1836, 706, 86, 679, 1008]
    lowerFloor := (699264187894449 / 500000000000000 : Rat)
    upperCeiling := (349632093958467 / 250000000000000 : Rat)
  },
  {
    cells := [1178, 1848, 1177]
    lowerFloor := (911269909252683 / 1000000000000000 : Rat)
    upperCeiling := (455634954795001 / 500000000000000 : Rat)
  },
  {
    cells := [1173, 1850, 1174]
    lowerFloor := (44490124121 / 48828125000 : Rat)
    upperCeiling := (911157742332859 / 1000000000000000 : Rat)
  },
  {
    cells := [1001, 698, 93, 701, 1834, 702, 92, 697, 1002]
    lowerFloor := (352266656113821 / 250000000000000 : Rat)
    upperCeiling := (1409066624501 / 1000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1456, 1460, 1456]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [1456, 1460, 1456]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [1806, 1631]
    lowerFloor := (693146528317851 / 1000000000000000 : Rat)
    upperCeiling := (346573616987493 / 500000000000000 : Rat)
  },
  {
    cells := [1630, 1807]
    lowerFloor := (27725861132717 / 40000000000000 : Rat)
    upperCeiling := (693147233974979 / 1000000000000000 : Rat)
  },
  {
    cells := [67, 1939, 66]
    lowerFloor := (270139764207 / 250000000000000 : Rat)
    upperCeiling := (270491931529 / 250000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [676, 1913, 675]
    lowerFloor := (63839284178697 / 200000000000000 : Rat)
    upperCeiling := (79799179783757 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [675, 1913, 676]
    lowerFloor := (63839284178697 / 200000000000000 : Rat)
    upperCeiling := (79799179783757 / 250000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1325, 1333, 1326, 1334]
    lowerFloor := (693146854433233 / 500000000000000 : Rat)
    upperCeiling := (693147207272553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1684, 1753]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [296, 1119, 298, 1031, 1033, 295, 1032, 1034, 1118, 297]
    lowerFloor := (1902716941254583 / 1000000000000000 : Rat)
    upperCeiling := (951358471275131 / 500000000000000 : Rat)
  },
  {
    cells := [675, 1913, 676]
    lowerFloor := (63839284178697 / 200000000000000 : Rat)
    upperCeiling := (79799179783757 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [67, 1939, 66]
    lowerFloor := (270139764207 / 250000000000000 : Rat)
    upperCeiling := (270491931529 / 250000000000000 : Rat)
  },
  {
    cells := [818, 630, 631, 820, 919, 920, 630, 919, 628, 628, 629, 631, 920, 629, 819, 821]
    lowerFloor := (2598316665412399 / 1000000000000000 : Rat)
    upperCeiling := (2598316746357923 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1456, 1460, 1456]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [67, 1939, 66]
    lowerFloor := (270139764207 / 250000000000000 : Rat)
    upperCeiling := (270491931529 / 250000000000000 : Rat)
  },
  {
    cells := [1325, 1333, 1326, 1334]
    lowerFloor := (693146854433233 / 500000000000000 : Rat)
    upperCeiling := (693147207272553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1684, 1753]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [296, 1119, 298, 1031, 1033, 295, 1032, 1034, 1118, 297]
    lowerFloor := (1902716941254583 / 1000000000000000 : Rat)
    upperCeiling := (951358471275131 / 500000000000000 : Rat)
  },
  {
    cells := [675, 1913, 676]
    lowerFloor := (63839284178697 / 200000000000000 : Rat)
    upperCeiling := (79799179783757 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [67, 1939, 66]
    lowerFloor := (270139764207 / 250000000000000 : Rat)
    upperCeiling := (270491931529 / 250000000000000 : Rat)
  },
  {
    cells := [818, 630, 631, 820, 919, 920, 630, 919, 628, 628, 629, 631, 920, 629, 819, 821]
    lowerFloor := (2598316665412399 / 1000000000000000 : Rat)
    upperCeiling := (2598316746357923 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1456, 1460, 1456]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [67, 1939, 66]
    lowerFloor := (270139764207 / 250000000000000 : Rat)
    upperCeiling := (270491931529 / 250000000000000 : Rat)
  },
  {
    cells := [1157, 1858, 1158]
    lowerFloor := (909126777766123 / 1000000000000000 : Rat)
    upperCeiling := (909126778058251 / 1000000000000000 : Rat)
  },
  {
    cells := [334, 1577, 1576, 333]
    lowerFloor := (96136111211093 / 125000000000000 : Rat)
    upperCeiling := (192272491354453 / 250000000000000 : Rat)
  },
  {
    cells := [1129, 333, 1431, 1430, 334, 1128]
    lowerFloor := (1410437279762283 / 1000000000000000 : Rat)
    upperCeiling := (1410437285173131 / 1000000000000000 : Rat)
  },
  {
    cells := [324, 1584, 1585, 323]
    lowerFloor := (766568638448703 / 1000000000000000 : Rat)
    upperCeiling := (383284861705477 / 500000000000000 : Rat)
  },
  {
    cells := [1715, 1722]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1141, 323, 1420, 1421, 324, 1140]
    lowerFloor := (352188337677081 / 250000000000000 : Rat)
    upperCeiling := (22011771140053 / 15625000000000 : Rat)
  },
  {
    cells := [1719, 1718]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1462, 1455, 1461]
    lowerFloor := (137326535536641 / 125000000000000 : Rat)
    upperCeiling := (1098612284354201 / 1000000000000000 : Rat)
  },
  {
    cells := [1088, 1109, 1090, 1090, 1108, 1088]
    lowerFloor := (111981112442877 / 62500000000000 : Rat)
    upperCeiling := (895848899584803 / 500000000000000 : Rat)
  },
  {
    cells := [1133, 1861, 1132]
    lowerFloor := (445448044788399 / 500000000000000 : Rat)
    upperCeiling := (178179217934809 / 200000000000000 : Rat)
  },
  {
    cells := [1132, 1861, 1133]
    lowerFloor := (445448044788399 / 500000000000000 : Rat)
    upperCeiling := (178179217934809 / 200000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [624, 1531, 1532, 625]
    lowerFloor := (903269495218279 / 1000000000000000 : Rat)
    upperCeiling := (451634988704829 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [625, 1532, 1531, 624]
    lowerFloor := (903269495218279 / 1000000000000000 : Rat)
    upperCeiling := (451634988704829 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [683, 1911, 684]
    lowerFloor := (327434809717511 / 1000000000000000 : Rat)
    upperCeiling := (327435090746371 / 1000000000000000 : Rat)
  },
  {
    cells := [684, 1911, 683]
    lowerFloor := (327434809717511 / 1000000000000000 : Rat)
    upperCeiling := (327435090746371 / 1000000000000000 : Rat)
  },
  {
    cells := [1781, 1656]
    lowerFloor := (693146528316487 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1743, 1694]
    lowerFloor := (34657326415823 / 50000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [130, 1931, 131]
    lowerFloor := (891979020553 / 62500000000000 : Rat)
    upperCeiling := (89206436469 / 6250000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [716, 1902, 717]
    lowerFloor := (4797021238109 / 12500000000000 : Rat)
    upperCeiling := (95940470173639 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [717, 1902, 716]
    lowerFloor := (4797021238109 / 12500000000000 : Rat)
    upperCeiling := (95940470173639 / 250000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [18, 514, 515, 58, 591, 60, 516, 517, 590, 1872, 592, 518, 520, 59, 593, 61, 519, 521, 19]
    lowerFloor := (1116816021587689 / 1000000000000000 : Rat)
    upperCeiling := (558408012200533 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [717, 1902, 716]
    lowerFloor := (4797021238109 / 12500000000000 : Rat)
    upperCeiling := (95940470173639 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [130, 1931, 131]
    lowerFloor := (891979020553 / 62500000000000 : Rat)
    upperCeiling := (89206436469 / 6250000000000 : Rat)
  },
  {
    cells := [313, 314, 375, 1245, 377, 376, 380, 378, 1246, 381, 1243, 1244, 311, 379, 382, 312]
    lowerFloor := (1802029709453723 / 1000000000000000 : Rat)
    upperCeiling := (901014951043541 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [684, 1911, 683]
    lowerFloor := (327434809717511 / 1000000000000000 : Rat)
    upperCeiling := (327435090746371 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [130, 1931, 131]
    lowerFloor := (891979020553 / 62500000000000 : Rat)
    upperCeiling := (89206436469 / 6250000000000 : Rat)
  },
  {
    cells := [1290, 1291, 1364, 1365]
    lowerFloor := (693124626337887 / 500000000000000 : Rat)
    upperCeiling := (1386249843088493 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1668, 1769]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [18, 514, 515, 58, 591, 60, 516, 517, 590, 1872, 592, 518, 520, 59, 593, 61, 519, 521, 19]
    lowerFloor := (1116816021587689 / 1000000000000000 : Rat)
    upperCeiling := (558408012200533 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [717, 1902, 716]
    lowerFloor := (4797021238109 / 12500000000000 : Rat)
    upperCeiling := (95940470173639 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [130, 1931, 131]
    lowerFloor := (891979020553 / 62500000000000 : Rat)
    upperCeiling := (89206436469 / 6250000000000 : Rat)
  },
  {
    cells := [313, 314, 375, 1245, 377, 376, 380, 378, 1246, 381, 1243, 1244, 311, 379, 382, 312]
    lowerFloor := (1802029709453723 / 1000000000000000 : Rat)
    upperCeiling := (901014951043541 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [684, 1911, 683]
    lowerFloor := (327434809717511 / 1000000000000000 : Rat)
    upperCeiling := (327435090746371 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [130, 1931, 131]
    lowerFloor := (891979020553 / 62500000000000 : Rat)
    upperCeiling := (89206436469 / 6250000000000 : Rat)
  },
  {
    cells := [1290, 1291, 1364, 1365]
    lowerFloor := (693124626337887 / 500000000000000 : Rat)
    upperCeiling := (1386249843088493 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1668, 1769]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [461, 1552, 1551, 460]
    lowerFloor := (816096625990129 / 1000000000000000 : Rat)
    upperCeiling := (408048735312917 / 500000000000000 : Rat)
  },
  {
    cells := [1786, 1651]
    lowerFloor := (27725861132663 / 40000000000000 : Rat)
    upperCeiling := (693147233975097 / 1000000000000000 : Rat)
  },
  {
    cells := [19, 455, 759, 1520, 1521, 758, 454, 18]
    lowerFloor := (591120040668339 / 500000000000000 : Rat)
    upperCeiling := (591120113801137 / 500000000000000 : Rat)
  },
  {
    cells := [1787, 1650]
    lowerFloor := (693146528316577 / 1000000000000000 : Rat)
    upperCeiling := (693147233975097 / 1000000000000000 : Rat)
  },
  {
    cells := [12, 778, 1886, 779, 13]
    lowerFloor := (250604147697409 / 500000000000000 : Rat)
    upperCeiling := (501208354071643 / 1000000000000000 : Rat)
  },
  {
    cells := [13, 473, 745, 1524, 1525, 744, 472, 12]
    lowerFloor := (72898521438427 / 62500000000000 : Rat)
    upperCeiling := (1166376424281217 / 1000000000000000 : Rat)
  },
  {
    cells := [1010, 1263, 1293, 1264, 1009]
    lowerFloor := (1583568095467207 / 1000000000000000 : Rat)
    upperCeiling := (791784272112693 / 500000000000000 : Rat)
  },
  {
    cells := [1374, 1292, 1279, 1373]
    lowerFloor := (1385840456932493 / 1000000000000000 : Rat)
    upperCeiling := (1385840911037419 / 1000000000000000 : Rat)
  },
  {
    cells := [1009, 918, 947, 969, 948, 946, 917, 1010]
    lowerFloor := (1036969607325681 / 500000000000000 : Rat)
    upperCeiling := (10369697273329 / 5000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [732, 1895, 733]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [733, 1895, 732]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [1643, 1794]
    lowerFloor := (346573264158313 / 500000000000000 : Rat)
    upperCeiling := (693147233975093 / 1000000000000000 : Rat)
  },
  {
    cells := [1646, 1791]
    lowerFloor := (693146528316617 / 1000000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [234, 1927, 233]
    lowerFloor := (18296233055267 / 250000000000000 : Rat)
    upperCeiling := (73186057001983 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [752, 1888, 753]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [753, 1888, 752]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [893, 894, 223, 984, 221, 231, 232, 224, 985, 222, 988, 989, 887, 229, 230, 888]
    lowerFloor := (2259854331825813 / 1000000000000000 : Rat)
    upperCeiling := (2259854350816073 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [733, 1895, 732]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [753, 1888, 752]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1678, 1759]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [234, 1927, 233]
    lowerFloor := (18296233055267 / 250000000000000 : Rat)
    upperCeiling := (73186057001983 / 1000000000000000 : Rat)
  },
  {
    cells := [305, 306, 203, 1272, 199, 205, 206, 204, 1273, 200, 1270, 1271, 303, 201, 202, 304]
    lowerFloor := (1718547661283603 / 1000000000000000 : Rat)
    upperCeiling := (1718547994682471 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [733, 1895, 732]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [753, 1888, 752]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1681, 1756]
    lowerFloor := (27725861132659 / 40000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [234, 1927, 233]
    lowerFloor := (18296233055267 / 250000000000000 : Rat)
    upperCeiling := (73186057001983 / 1000000000000000 : Rat)
  },
  {
    cells := [160, 1143, 158, 1073, 1074, 161, 1075, 1076, 1142, 159]
    lowerFloor := (1837739920905269 / 1000000000000000 : Rat)
    upperCeiling := (114858745064579 / 62500000000000 : Rat)
  },
  {
    cells := [733, 1895, 732]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [753, 1888, 752]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1673, 1764]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [234, 1927, 233]
    lowerFloor := (18296233055267 / 250000000000000 : Rat)
    upperCeiling := (73186057001983 / 1000000000000000 : Rat)
  },
  {
    cells := [893, 894, 223, 984, 221, 231, 232, 224, 985, 222, 988, 989, 887, 229, 230, 888]
    lowerFloor := (2259854331825813 / 1000000000000000 : Rat)
    upperCeiling := (2259854350816073 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [753, 1888, 752]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [733, 1895, 732]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1678, 1759]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [234, 1927, 233]
    lowerFloor := (18296233055267 / 250000000000000 : Rat)
    upperCeiling := (73186057001983 / 1000000000000000 : Rat)
  },
  {
    cells := [305, 306, 203, 1272, 199, 205, 206, 204, 1273, 200, 1270, 1271, 303, 201, 202, 304]
    lowerFloor := (1718547661283603 / 1000000000000000 : Rat)
    upperCeiling := (1718547994682471 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [753, 1888, 752]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [733, 1895, 732]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1681, 1756]
    lowerFloor := (27725861132659 / 40000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [234, 1927, 233]
    lowerFloor := (18296233055267 / 250000000000000 : Rat)
    upperCeiling := (73186057001983 / 1000000000000000 : Rat)
  },
  {
    cells := [160, 1143, 158, 1073, 1074, 161, 1075, 1076, 1142, 159]
    lowerFloor := (1837739920905269 / 1000000000000000 : Rat)
    upperCeiling := (114858745064579 / 62500000000000 : Rat)
  },
  {
    cells := [753, 1888, 752]
    lowerFloor := (434651560055609 / 1000000000000000 : Rat)
    upperCeiling := (434651704990837 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [733, 1895, 732]
    lowerFloor := (82187598667489 / 200000000000000 : Rat)
    upperCeiling := (410938141767129 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1673, 1764]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [234, 1927, 233]
    lowerFloor := (18296233055267 / 250000000000000 : Rat)
    upperCeiling := (73186057001983 / 1000000000000000 : Rat)
  },
  {
    cells := [1225, 1393, 1395, 1226]
    lowerFloor := (1374768829139451 / 1000000000000000 : Rat)
    upperCeiling := (1374768850036903 / 1000000000000000 : Rat)
  },
  {
    cells := [1402, 1494, 1401]
    lowerFloor := (218224707909449 / 200000000000000 : Rat)
    upperCeiling := (1091123542046491 / 1000000000000000 : Rat)
  },
  {
    cells := [895, 886, 883, 824, 845, 853, 829, 884, 885, 896]
    lowerFloor := (2300100364416433 / 1000000000000000 : Rat)
    upperCeiling := (1150050196543867 / 500000000000000 : Rat)
  },
  {
    cells := [1168, 1853, 1167]
    lowerFloor := (227487174856399 / 250000000000000 : Rat)
    upperCeiling := (454974349867123 / 500000000000000 : Rat)
  },
  {
    cells := [435, 1569, 1570, 434]
    lowerFloor := (32579879487529 / 40000000000000 : Rat)
    upperCeiling := (814497838821869 / 1000000000000000 : Rat)
  },
  {
    cells := [146, 411, 388, 1411, 1063, 1064, 1410, 389, 410, 147]
    lowerFloor := (61643701695871 / 40000000000000 : Rat)
    upperCeiling := (192636567832551 / 125000000000000 : Rat)
  },
  {
    cells := [443, 1565, 1566, 442]
    lowerFloor := (815256307214903 / 1000000000000000 : Rat)
    upperCeiling := (163051431100093 / 200000000000000 : Rat)
  },
  {
    cells := [447, 1562, 1561, 446]
    lowerFloor := (81546506917831 / 100000000000000 : Rat)
    upperCeiling := (407732958275687 / 500000000000000 : Rat)
  },
  {
    cells := [154, 393, 390, 1441, 1025, 1026, 1440, 391, 392, 155]
    lowerFloor := (1537772261262903 / 1000000000000000 : Rat)
    upperCeiling := (1537772261730673 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [751, 1889, 750]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [750, 1889, 751]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [1805, 1632]
    lowerFloor := (86643316039731 / 125000000000000 : Rat)
    upperCeiling := (346573616987493 / 500000000000000 : Rat)
  },
  {
    cells := [1804, 1633]
    lowerFloor := (86643316039729 / 125000000000000 : Rat)
    upperCeiling := (173286808493747 / 250000000000000 : Rat)
  },
  {
    cells := [235, 1926, 236]
    lowerFloor := (36611788342951 / 500000000000000 : Rat)
    upperCeiling := (18306175325943 / 250000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [734, 1894, 735]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [735, 1894, 734]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [163, 1145, 165, 1069, 1071, 162, 1070, 1072, 1144, 164]
    lowerFloor := (73513396918359 / 40000000000000 : Rat)
    upperCeiling := (1837834923090881 / 1000000000000000 : Rat)
  },
  {
    cells := [750, 1889, 751]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [735, 1894, 734]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1673, 1764]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [235, 1926, 236]
    lowerFloor := (36611788342951 / 500000000000000 : Rat)
    upperCeiling := (18306175325943 / 250000000000000 : Rat)
  },
  {
    cells := [307, 308, 191, 1266, 195, 193, 194, 192, 1267, 196, 1268, 1269, 309, 197, 198, 310]
    lowerFloor := (68761713800463 / 40000000000000 : Rat)
    upperCeiling := (214880397196901 / 125000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [750, 1889, 751]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [735, 1894, 734]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1665, 1772]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [235, 1926, 236]
    lowerFloor := (36611788342951 / 500000000000000 : Rat)
    upperCeiling := (18306175325943 / 250000000000000 : Rat)
  },
  {
    cells := [825, 826, 237, 1019, 239, 241, 242, 238, 1020, 240, 1017, 1018, 827, 243, 244, 828]
    lowerFloor := (224181311389177 / 100000000000000 : Rat)
    upperCeiling := (2241813114256077 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [750, 1889, 751]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [735, 1894, 734]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1676, 1761]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [235, 1926, 236]
    lowerFloor := (36611788342951 / 500000000000000 : Rat)
    upperCeiling := (18306175325943 / 250000000000000 : Rat)
  },
  {
    cells := [163, 1145, 165, 1069, 1071, 162, 1070, 1072, 1144, 164]
    lowerFloor := (73513396918359 / 40000000000000 : Rat)
    upperCeiling := (1837834923090881 / 1000000000000000 : Rat)
  },
  {
    cells := [735, 1894, 734]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [750, 1889, 751]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1673, 1764]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [235, 1926, 236]
    lowerFloor := (36611788342951 / 500000000000000 : Rat)
    upperCeiling := (18306175325943 / 250000000000000 : Rat)
  },
  {
    cells := [307, 308, 191, 1266, 195, 193, 194, 192, 1267, 196, 1268, 1269, 309, 197, 198, 310]
    lowerFloor := (68761713800463 / 40000000000000 : Rat)
    upperCeiling := (214880397196901 / 125000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [735, 1894, 734]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [750, 1889, 751]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1665, 1772]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [235, 1926, 236]
    lowerFloor := (36611788342951 / 500000000000000 : Rat)
    upperCeiling := (18306175325943 / 250000000000000 : Rat)
  },
  {
    cells := [825, 826, 237, 1019, 239, 241, 242, 238, 1020, 240, 1017, 1018, 827, 243, 244, 828]
    lowerFloor := (224181311389177 / 100000000000000 : Rat)
    upperCeiling := (2241813114256077 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [735, 1894, 734]
    lowerFloor := (410972371830413 / 1000000000000000 : Rat)
    upperCeiling := (410972520230309 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [750, 1889, 751]
    lowerFloor := (868459689479 / 2000000000000 : Rat)
    upperCeiling := (434229989292527 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1676, 1761]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [235, 1926, 236]
    lowerFloor := (36611788342951 / 500000000000000 : Rat)
    upperCeiling := (18306175325943 / 250000000000000 : Rat)
  },
  {
    cells := [450, 1557, 1558, 451]
    lowerFloor := (815858913169629 / 1000000000000000 : Rat)
    upperCeiling := (815859758831413 / 1000000000000000 : Rat)
  },
  {
    cells := [458, 1553, 1554, 459]
    lowerFloor := (408020889267863 / 500000000000000 : Rat)
    upperCeiling := (204010655851927 / 250000000000000 : Rat)
  },
  {
    cells := [398, 156, 1027, 1439, 403, 402, 1438, 1028, 157, 399]
    lowerFloor := (1539034158947141 / 1000000000000000 : Rat)
    upperCeiling := (1539034159470071 / 1000000000000000 : Rat)
  },
  {
    cells := [452, 1556, 1555, 453]
    lowerFloor := (203985035832279 / 250000000000000 : Rat)
    upperCeiling := (2549815589499 / 3125000000000 : Rat)
  },
  {
    cells := [1166, 1854, 1165]
    lowerFloor := (454880715971749 / 500000000000000 : Rat)
    upperCeiling := (909761432248297 / 1000000000000000 : Rat)
  },
  {
    cells := [412, 151, 1051, 1412, 405, 404, 1413, 1052, 150, 413]
    lowerFloor := (1542451729098777 / 1000000000000000 : Rat)
    upperCeiling := (308490345894881 / 200000000000000 : Rat)
  },
  {
    cells := [1399, 1495, 1398]
    lowerFloor := (1088897384227833 / 1000000000000000 : Rat)
    upperCeiling := (1088897388718707 / 1000000000000000 : Rat)
  },
  {
    cells := [1148, 1444, 1445, 1149]
    lowerFloor := (1343683759972067 / 1000000000000000 : Rat)
    upperCeiling := (335920940029423 / 250000000000000 : Rat)
  },
  {
    cells := [842, 816, 923, 936, 844, 841, 937, 924, 817, 840]
    lowerFloor := (1147533985700481 / 500000000000000 : Rat)
    upperCeiling := (143441755999791 / 62500000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [725, 1898, 724]
    lowerFloor := (47981644448511 / 125000000000000 : Rat)
    upperCeiling := (47981667137487 / 125000000000000 : Rat)
  },
  {
    cells := [724, 1898, 725]
    lowerFloor := (47981644448511 / 125000000000000 : Rat)
    upperCeiling := (47981667137487 / 125000000000000 : Rat)
  },
  {
    cells := [1723, 1714]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1724, 1713]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [122, 1935, 123]
    lowerFloor := (675098813951 / 50000000000000 : Rat)
    upperCeiling := (13503344258403 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [687, 1909, 688]
    lowerFloor := (164937869611197 / 500000000000000 : Rat)
    upperCeiling := (329876015284423 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [688, 1909, 687]
    lowerFloor := (164937869611197 / 500000000000000 : Rat)
    upperCeiling := (329876015284423 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1358, 1359, 1296, 1297]
    lowerFloor := (1386293708773089 / 1000000000000000 : Rat)
    upperCeiling := (1386294414050429 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1675, 1762]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [268, 270, 343, 1247, 344, 345, 349, 347, 1249, 348, 1248, 1250, 267, 346, 350, 269]
    lowerFloor := (1793729070956699 / 1000000000000000 : Rat)
    upperCeiling := (56054039783599 / 31250000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [688, 1909, 687]
    lowerFloor := (164937869611197 / 500000000000000 : Rat)
    upperCeiling := (329876015284423 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [122, 1935, 123]
    lowerFloor := (675098813951 / 50000000000000 : Rat)
    upperCeiling := (13503344258403 / 1000000000000000 : Rat)
  },
  {
    cells := [79, 530, 532, 42, 583, 44, 534, 536, 582, 1868, 584, 531, 535, 43, 585, 45, 533, 537, 78]
    lowerFloor := (578825861646627 / 500000000000000 : Rat)
    upperCeiling := (46306069006401 / 40000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [724, 1898, 725]
    lowerFloor := (47981644448511 / 125000000000000 : Rat)
    upperCeiling := (47981667137487 / 125000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [122, 1935, 123]
    lowerFloor := (675098813951 / 50000000000000 : Rat)
    upperCeiling := (13503344258403 / 1000000000000000 : Rat)
  },
  {
    cells := [1358, 1359, 1296, 1297]
    lowerFloor := (1386293708773089 / 1000000000000000 : Rat)
    upperCeiling := (1386294414050429 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1675, 1762]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [268, 270, 343, 1247, 344, 345, 349, 347, 1249, 348, 1248, 1250, 267, 346, 350, 269]
    lowerFloor := (1793729070956699 / 1000000000000000 : Rat)
    upperCeiling := (56054039783599 / 31250000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [688, 1909, 687]
    lowerFloor := (164937869611197 / 500000000000000 : Rat)
    upperCeiling := (329876015284423 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [122, 1935, 123]
    lowerFloor := (675098813951 / 50000000000000 : Rat)
    upperCeiling := (13503344258403 / 1000000000000000 : Rat)
  },
  {
    cells := [79, 530, 532, 42, 583, 44, 534, 536, 582, 1868, 584, 531, 535, 43, 585, 45, 533, 537, 78]
    lowerFloor := (578825861646627 / 500000000000000 : Rat)
    upperCeiling := (46306069006401 / 40000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [724, 1898, 725]
    lowerFloor := (47981644448511 / 125000000000000 : Rat)
    upperCeiling := (47981667137487 / 125000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [122, 1935, 123]
    lowerFloor := (675098813951 / 50000000000000 : Rat)
    upperCeiling := (13503344258403 / 1000000000000000 : Rat)
  },
  {
    cells := [1287, 1367, 1368, 1288]
    lowerFloor := (346507893777291 / 250000000000000 : Rat)
    upperCeiling := (1386032029447407 / 1000000000000000 : Rat)
  },
  {
    cells := [929, 1381, 1371, 1380, 930]
    lowerFloor := (192628968561347 / 125000000000000 : Rat)
    upperCeiling := (770515896229671 / 500000000000000 : Rat)
  },
  {
    cells := [976, 930, 963, 960, 959, 965, 929, 977]
    lowerFloor := (2077746950606663 / 1000000000000000 : Rat)
    upperCeiling := (519436748647679 / 250000000000000 : Rat)
  },
  {
    cells := [95, 794, 1880, 795, 94]
    lowerFloor := (551352213009033 / 1000000000000000 : Rat)
    upperCeiling := (551352247051317 / 1000000000000000 : Rat)
  },
  {
    cells := [1726, 1711]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [429, 94, 1512, 770, 771, 1513, 95, 428]
    lowerFloor := (1203434768739427 / 1000000000000000 : Rat)
    upperCeiling := (48137392121649 / 40000000000000 : Rat)
  },
  {
    cells := [1727, 1710]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [477, 1543, 1544, 476]
    lowerFloor := (409490933351953 / 500000000000000 : Rat)
    upperCeiling := (204745674848573 / 250000000000000 : Rat)
  },
  {
    cells := [465, 78, 1508, 763, 762, 1509, 79, 464]
    lowerFloor := (603979620192237 / 500000000000000 : Rat)
    upperCeiling := (48318371010687 / 40000000000000 : Rat)
  },
  {
    cells := [496, 1539, 1538, 497]
    lowerFloor := (26475773886617 / 31250000000000 : Rat)
    upperCeiling := (423612733192943 / 500000000000000 : Rat)
  },
  {
    cells := [497, 1538, 1539, 496]
    lowerFloor := (26475773886617 / 31250000000000 : Rat)
    upperCeiling := (423612733192943 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [172, 973, 1864, 971, 173]
    lowerFloor := (789131503503059 / 1000000000000000 : Rat)
    upperCeiling := (770636234509 / 976562500000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [173, 971, 1864, 973, 172]
    lowerFloor := (789131503503059 / 1000000000000000 : Rat)
    upperCeiling := (770636234509 / 976562500000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [721, 1900, 720]
    lowerFloor := (383849918499551 / 1000000000000000 : Rat)
    upperCeiling := (3838501000161 / 10000000000000 : Rat)
  },
  {
    cells := [720, 1900, 721]
    lowerFloor := (383849918499551 / 1000000000000000 : Rat)
    upperCeiling := (3838501000161 / 10000000000000 : Rat)
  },
  {
    cells := [1748, 1689]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1690, 1747]
    lowerFloor := (693146528316473 / 1000000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [126, 1933, 127]
    lowerFloor := (13521111875101 / 1000000000000000 : Rat)
    upperCeiling := (6761239894583 / 500000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [691, 1907, 692]
    lowerFloor := (329903009646219 / 1000000000000000 : Rat)
    upperCeiling := (3299032856531 / 10000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [692, 1907, 691]
    lowerFloor := (329903009646219 / 1000000000000000 : Rat)
    upperCeiling := (3299032856531 / 10000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [255, 256, 363, 1259, 364, 359, 361, 365, 1260, 366, 1257, 1258, 257, 360, 362, 258]
    lowerFloor := (896143578844857 / 500000000000000 : Rat)
    upperCeiling := (1792287361578379 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [692, 1907, 691]
    lowerFloor := (329903009646219 / 1000000000000000 : Rat)
    upperCeiling := (3299032856531 / 10000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [126, 1933, 127]
    lowerFloor := (13521111875101 / 1000000000000000 : Rat)
    upperCeiling := (6761239894583 / 500000000000000 : Rat)
  },
  {
    cells := [82, 538, 539, 50, 574, 51, 540, 541, 576, 1867, 577, 542, 544, 52, 575, 53, 543, 545, 83]
    lowerFloor := (28957490579333 / 25000000000000 : Rat)
    upperCeiling := (1158299625027051 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [720, 1900, 721]
    lowerFloor := (383849918499551 / 1000000000000000 : Rat)
    upperCeiling := (3838501000161 / 10000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [126, 1933, 127]
    lowerFloor := (13521111875101 / 1000000000000000 : Rat)
    upperCeiling := (6761239894583 / 500000000000000 : Rat)
  },
  {
    cells := [1237, 1238, 1388, 1389]
    lowerFloor := (275887366877469 / 200000000000000 : Rat)
    upperCeiling := (689718444179447 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1680, 1757]
    lowerFloor := (27725861132659 / 40000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [255, 256, 363, 1259, 364, 359, 361, 365, 1260, 366, 1257, 1258, 257, 360, 362, 258]
    lowerFloor := (896143578844857 / 500000000000000 : Rat)
    upperCeiling := (1792287361578379 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [692, 1907, 691]
    lowerFloor := (329903009646219 / 1000000000000000 : Rat)
    upperCeiling := (3299032856531 / 10000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [126, 1933, 127]
    lowerFloor := (13521111875101 / 1000000000000000 : Rat)
    upperCeiling := (6761239894583 / 500000000000000 : Rat)
  },
  {
    cells := [82, 538, 539, 50, 574, 51, 540, 541, 576, 1867, 577, 542, 544, 52, 575, 53, 543, 545, 83]
    lowerFloor := (28957490579333 / 25000000000000 : Rat)
    upperCeiling := (1158299625027051 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [720, 1900, 721]
    lowerFloor := (383849918499551 / 1000000000000000 : Rat)
    upperCeiling := (3838501000161 / 10000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [126, 1933, 127]
    lowerFloor := (13521111875101 / 1000000000000000 : Rat)
    upperCeiling := (6761239894583 / 500000000000000 : Rat)
  },
  {
    cells := [1237, 1238, 1388, 1389]
    lowerFloor := (275887366877469 / 200000000000000 : Rat)
    upperCeiling := (689718444179447 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1680, 1757]
    lowerFloor := (27725861132659 / 40000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [98, 788, 1883, 789, 99]
    lowerFloor := (110232440617353 / 200000000000000 : Rat)
    upperCeiling := (22046489488667 / 40000000000000 : Rat)
  },
  {
    cells := [1637, 1800]
    lowerFloor := (693146528317123 / 1000000000000000 : Rat)
    upperCeiling := (693147233975051 / 1000000000000000 : Rat)
  },
  {
    cells := [98, 423, 772, 1518, 1519, 773, 422, 99]
    lowerFloor := (601291323895383 / 500000000000000 : Rat)
    upperCeiling := (601291341043423 / 500000000000000 : Rat)
  },
  {
    cells := [1638, 1799]
    lowerFloor := (693146528317099 / 1000000000000000 : Rat)
    upperCeiling := (693147233975053 / 1000000000000000 : Rat)
  },
  {
    cells := [468, 1548, 1547, 469]
    lowerFloor := (817133738750221 / 1000000000000000 : Rat)
    upperCeiling := (817134578975609 / 1000000000000000 : Rat)
  },
  {
    cells := [82, 439, 764, 1506, 1507, 765, 438, 83]
    lowerFloor := (1207497187408373 / 1000000000000000 : Rat)
    upperCeiling := (1207497221415637 / 1000000000000000 : Rat)
  },
  {
    cells := [1152, 1483, 1378, 1188]
    lowerFloor := (669415495938631 / 500000000000000 : Rat)
    upperCeiling := (334707748233687 / 250000000000000 : Rat)
  },
  {
    cells := [834, 1228, 1493, 1227, 830]
    lowerFloor := (58515829396419 / 40000000000000 : Rat)
    upperCeiling := (73144788090877 / 50000000000000 : Rat)
  },
  {
    cells := [834, 838, 954, 992, 1366, 955, 833, 830]
    lowerFloor := (401520371220239 / 200000000000000 : Rat)
    upperCeiling := (250950257678373 / 125000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [741, 1891, 740]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [740, 1891, 741]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [1709, 1728]
    lowerFloor := (13862930566329 / 20000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1703, 1734]
    lowerFloor := (693146528316453 / 1000000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [188, 1930, 187]
    lowerFloor := (67959766415537 / 1000000000000000 : Rat)
    upperCeiling := (8495114163233 / 125000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [710, 1904, 709]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [709, 1904, 710]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [272, 1104, 271, 1053, 1054, 274, 1055, 1056, 1105, 273]
    lowerFloor := (1900573409619949 / 1000000000000000 : Rat)
    upperCeiling := (380114682060037 / 200000000000000 : Rat)
  },
  {
    cells := [740, 1891, 741]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [709, 1904, 710]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1662, 1775]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [188, 1930, 187]
    lowerFloor := (67959766415537 / 1000000000000000 : Rat)
    upperCeiling := (8495114163233 / 125000000000000 : Rat)
  },
  {
    cells := [91, 558, 559, 112, 487, 113, 560, 561, 485, 1875, 484, 554, 556, 114, 486, 115, 555, 557, 90]
    lowerFloor := (280059958468561 / 250000000000000 : Rat)
    upperCeiling := (1120239836985843 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [740, 1891, 741]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [709, 1904, 710]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1674, 1763]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [188, 1930, 187]
    lowerFloor := (67959766415537 / 1000000000000000 : Rat)
    upperCeiling := (8495114163233 / 125000000000000 : Rat)
  },
  {
    cells := [418, 1419, 419, 800, 801, 420, 802, 803, 1418, 421]
    lowerFloor := (1743257866848759 / 1000000000000000 : Rat)
    upperCeiling := (435814466749097 / 250000000000000 : Rat)
  },
  {
    cells := [740, 1891, 741]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [709, 1904, 710]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1666, 1771]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [188, 1930, 187]
    lowerFloor := (67959766415537 / 1000000000000000 : Rat)
    upperCeiling := (8495114163233 / 125000000000000 : Rat)
  },
  {
    cells := [272, 1104, 271, 1053, 1054, 274, 1055, 1056, 1105, 273]
    lowerFloor := (1900573409619949 / 1000000000000000 : Rat)
    upperCeiling := (380114682060037 / 200000000000000 : Rat)
  },
  {
    cells := [709, 1904, 710]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [740, 1891, 741]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1662, 1775]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [188, 1930, 187]
    lowerFloor := (67959766415537 / 1000000000000000 : Rat)
    upperCeiling := (8495114163233 / 125000000000000 : Rat)
  },
  {
    cells := [91, 558, 559, 112, 487, 113, 560, 561, 485, 1875, 484, 554, 556, 114, 486, 115, 555, 557, 90]
    lowerFloor := (280059958468561 / 250000000000000 : Rat)
    upperCeiling := (1120239836985843 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [709, 1904, 710]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [740, 1891, 741]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1674, 1763]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [188, 1930, 187]
    lowerFloor := (67959766415537 / 1000000000000000 : Rat)
    upperCeiling := (8495114163233 / 125000000000000 : Rat)
  },
  {
    cells := [418, 1419, 419, 800, 801, 420, 802, 803, 1418, 421]
    lowerFloor := (1743257866848759 / 1000000000000000 : Rat)
    upperCeiling := (435814466749097 / 250000000000000 : Rat)
  },
  {
    cells := [709, 1904, 710]
    lowerFloor := (178177607180123 / 500000000000000 : Rat)
    upperCeiling := (356355440374531 / 1000000000000000 : Rat)
  },
  {
    cells := [740, 1891, 741]
    lowerFloor := (424260500692807 / 1000000000000000 : Rat)
    upperCeiling := (84852128385847 / 200000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1666, 1771]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [188, 1930, 187]
    lowerFloor := (67959766415537 / 1000000000000000 : Rat)
    upperCeiling := (8495114163233 / 125000000000000 : Rat)
  },
  {
    cells := [88, 799, 1878, 798, 89]
    lowerFloor := (276626454536881 / 500000000000000 : Rat)
    upperCeiling := (553252942235477 / 1000000000000000 : Rat)
  },
  {
    cells := [1184, 1845, 1183]
    lowerFloor := (911634095830613 / 1000000000000000 : Rat)
    upperCeiling := (911634096176317 / 1000000000000000 : Rat)
  },
  {
    cells := [88, 682, 704, 1004, 1837, 1003, 703, 681, 89]
    lowerFloor := (699275527465881 / 500000000000000 : Rat)
    upperCeiling := (1398551054976717 / 1000000000000000 : Rat)
  },
  {
    cells := [1176, 1849, 1175]
    lowerFloor := (455583302370253 / 500000000000000 : Rat)
    upperCeiling := (227791651268871 / 250000000000000 : Rat)
  },
  {
    cells := [1179, 1847, 1180]
    lowerFloor := (18225577016229 / 20000000000000 : Rat)
    upperCeiling := (911278851148971 / 1000000000000000 : Rat)
  },
  {
    cells := [91, 700, 696, 1006, 1835, 1005, 695, 699, 90]
    lowerFloor := (1408978253469701 / 1000000000000000 : Rat)
    upperCeiling := (1408978253515389 / 1000000000000000 : Rat)
  },
  {
    cells := [1476, 1442, 1477]
    lowerFloor := (1098108428908433 / 1000000000000000 : Rat)
    upperCeiling := (1098108428986361 / 1000000000000000 : Rat)
  },
  {
    cells := [996, 1234, 1390, 1233, 995]
    lowerFloor := (393460343831967 / 250000000000000 : Rat)
    upperCeiling := (314768283250539 / 200000000000000 : Rat)
  },
  {
    cells := [996, 912, 909, 831, 876, 832, 910, 911, 995]
    lowerFloor := (1092530265213211 / 500000000000000 : Rat)
    upperCeiling := (1092530286340771 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [690, 1908, 689]
    lowerFloor := (329875948706961 / 1000000000000000 : Rat)
    upperCeiling := (164938112384283 / 500000000000000 : Rat)
  },
  {
    cells := [689, 1908, 690]
    lowerFloor := (329875948706961 / 1000000000000000 : Rat)
    upperCeiling := (164938112384283 / 500000000000000 : Rat)
  },
  {
    cells := [1635, 1802]
    lowerFloor := (17328663207933 / 25000000000000 : Rat)
    upperCeiling := (346573616987517 / 500000000000000 : Rat)
  },
  {
    cells := [1636, 1801]
    lowerFloor := (693146528317273 / 1000000000000000 : Rat)
    upperCeiling := (346573616987519 / 500000000000000 : Rat)
  },
  {
    cells := [121, 1936, 120]
    lowerFloor := (1686535671233 / 125000000000000 : Rat)
    upperCeiling := (3373413345593 / 250000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [727, 1897, 726]
    lowerFloor := (383854021375729 / 1000000000000000 : Rat)
    upperCeiling := (383854202886269 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [726, 1897, 727]
    lowerFloor := (383854021375729 / 1000000000000000 : Rat)
    upperCeiling := (383854202886269 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1356, 1357, 1298, 1299]
    lowerFloor := (1386293708940579 / 1000000000000000 : Rat)
    upperCeiling := (1386294414459287 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1670, 1767]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [81, 522, 524, 41, 580, 40, 526, 528, 581, 1869, 579, 523, 527, 39, 578, 38, 525, 529, 80]
    lowerFloor := (289411988094791 / 250000000000000 : Rat)
    upperCeiling := (578823977123003 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [726, 1897, 727]
    lowerFloor := (383854021375729 / 1000000000000000 : Rat)
    upperCeiling := (383854202886269 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [121, 1936, 120]
    lowerFloor := (1686535671233 / 125000000000000 : Rat)
    upperCeiling := (3373413345593 / 250000000000000 : Rat)
  },
  {
    cells := [264, 266, 339, 1251, 335, 340, 342, 341, 1253, 337, 1252, 1254, 263, 336, 338, 265]
    lowerFloor := (358745653082417 / 200000000000000 : Rat)
    upperCeiling := (1793728467531617 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [689, 1908, 690]
    lowerFloor := (329875948706961 / 1000000000000000 : Rat)
    upperCeiling := (164938112384283 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [121, 1936, 120]
    lowerFloor := (1686535671233 / 125000000000000 : Rat)
    upperCeiling := (3373413345593 / 250000000000000 : Rat)
  },
  {
    cells := [1356, 1357, 1298, 1299]
    lowerFloor := (1386293708940579 / 1000000000000000 : Rat)
    upperCeiling := (1386294414459287 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1670, 1767]
    lowerFloor := (173286632079119 / 250000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [81, 522, 524, 41, 580, 40, 526, 528, 581, 1869, 579, 523, 527, 39, 578, 38, 525, 529, 80]
    lowerFloor := (289411988094791 / 250000000000000 : Rat)
    upperCeiling := (578823977123003 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [726, 1897, 727]
    lowerFloor := (383854021375729 / 1000000000000000 : Rat)
    upperCeiling := (383854202886269 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [121, 1936, 120]
    lowerFloor := (1686535671233 / 125000000000000 : Rat)
    upperCeiling := (3373413345593 / 250000000000000 : Rat)
  },
  {
    cells := [264, 266, 339, 1251, 335, 340, 342, 341, 1253, 337, 1252, 1254, 263, 336, 338, 265]
    lowerFloor := (358745653082417 / 200000000000000 : Rat)
    upperCeiling := (1793728467531617 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [689, 1908, 690]
    lowerFloor := (329875948706961 / 1000000000000000 : Rat)
    upperCeiling := (164938112384283 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [121, 1936, 120]
    lowerFloor := (1686535671233 / 125000000000000 : Rat)
    upperCeiling := (3373413345593 / 250000000000000 : Rat)
  },
  {
    cells := [928, 1382, 1372, 1383, 927]
    lowerFloor := (1540974902218547 / 1000000000000000 : Rat)
    upperCeiling := (308194989178681 / 200000000000000 : Rat)
  },
  {
    cells := [1285, 1370, 1369, 1286]
    lowerFloor := (693014776305727 / 500000000000000 : Rat)
    upperCeiling := (2165671884621 / 1562500000000 : Rat)
  },
  {
    cells := [928, 961, 979, 964, 966, 978, 962, 927]
    lowerFloor := (32464651812423 / 15625000000000 : Rat)
    upperCeiling := (103886887984271 / 50000000000000 : Rat)
  },
  {
    cells := [478, 1542, 1541, 479]
    lowerFloor := (409491095524219 / 500000000000000 : Rat)
    upperCeiling := (163796604747509 / 200000000000000 : Rat)
  },
  {
    cells := [1712, 1725]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [81, 760, 467, 1511, 1510, 466, 761, 80]
    lowerFloor := (1207959374682991 / 1000000000000000 : Rat)
    upperCeiling := (9663675276527 / 8000000000000 : Rat)
  },
  {
    cells := [1721, 1716]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [96, 793, 1881, 792, 97]
    lowerFloor := (275675928345661 / 500000000000000 : Rat)
    upperCeiling := (551351890733849 / 1000000000000000 : Rat)
  },
  {
    cells := [96, 769, 426, 1514, 1515, 427, 768, 97]
    lowerFloor := (1203434253999881 / 1000000000000000 : Rat)
    upperCeiling := (1203434288301877 / 1000000000000000 : Rat)
  },
  {
    cells := [133, 902, 1876, 901, 132]
    lowerFloor := (171367444160089 / 250000000000000 : Rat)
    upperCeiling := (42841862231703 / 62500000000000 : Rat)
  },
  {
    cells := [132, 901, 1876, 902, 133]
    lowerFloor := (171367444160089 / 250000000000000 : Rat)
    upperCeiling := (42841862231703 / 62500000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [605, 1533, 1534, 604]
    lowerFloor := (13643487640539 / 15625000000000 : Rat)
    upperCeiling := (436591900986801 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [604, 1534, 1533, 605]
    lowerFloor := (13643487640539 / 15625000000000 : Rat)
    upperCeiling := (436591900986801 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1503, 1193, 1502]
    lowerFloor := (130877659400609 / 125000000000000 : Rat)
    upperCeiling := (261755322139921 / 250000000000000 : Rat)
  },
  {
    cells := [1502, 1193, 1503]
    lowerFloor := (130877659400609 / 125000000000000 : Rat)
    upperCeiling := (261755322139921 / 250000000000000 : Rat)
  },
  {
    cells := [1622, 1815]
    lowerFloor := (693146528333773 / 1000000000000000 : Rat)
    upperCeiling := (21660851061639 / 31250000000000 : Rat)
  },
  {
    cells := [1814, 1623]
    lowerFloor := (346573264166863 / 500000000000000 : Rat)
    upperCeiling := (693147233972459 / 1000000000000000 : Rat)
  },
  {
    cells := [63, 1941, 62]
    lowerFloor := (428839060479 / 500000000000000 : Rat)
    upperCeiling := (214771843237 / 250000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [674, 1914, 673]
    lowerFloor := (15959452341293 / 50000000000000 : Rat)
    upperCeiling := (319189345083123 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [673, 1914, 674]
    lowerFloor := (15959452341293 / 50000000000000 : Rat)
    upperCeiling := (319189345083123 / 1000000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [286, 1113, 285, 1043, 1045, 284, 1044, 1046, 1112, 283]
    lowerFloor := (1902701778535029 / 1000000000000000 : Rat)
    upperCeiling := (951350889911313 / 500000000000000 : Rat)
  },
  {
    cells := [673, 1914, 674]
    lowerFloor := (15959452341293 / 50000000000000 : Rat)
    upperCeiling := (319189345083123 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [63, 1941, 62]
    lowerFloor := (428839060479 / 500000000000000 : Rat)
    upperCeiling := (214771843237 / 250000000000000 : Rat)
  },
  {
    cells := [864, 609, 611, 865, 879, 880, 613, 856, 612, 608, 610, 615, 857, 614, 866, 867]
    lowerFloor := (103923979818553 / 40000000000000 : Rat)
    upperCeiling := (2598099515638991 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1502, 1193, 1503]
    lowerFloor := (130877659400609 / 125000000000000 : Rat)
    upperCeiling := (261755322139921 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [63, 1941, 62]
    lowerFloor := (428839060479 / 500000000000000 : Rat)
    upperCeiling := (214771843237 / 250000000000000 : Rat)
  },
  {
    cells := [1308, 1309, 1350, 1351]
    lowerFloor := (1386293708877803 / 1000000000000000 : Rat)
    upperCeiling := (1386294414543671 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1685, 1752]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [286, 1113, 285, 1043, 1045, 284, 1044, 1046, 1112, 283]
    lowerFloor := (1902701778535029 / 1000000000000000 : Rat)
    upperCeiling := (951350889911313 / 500000000000000 : Rat)
  },
  {
    cells := [673, 1914, 674]
    lowerFloor := (15959452341293 / 50000000000000 : Rat)
    upperCeiling := (319189345083123 / 1000000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [63, 1941, 62]
    lowerFloor := (428839060479 / 500000000000000 : Rat)
    upperCeiling := (214771843237 / 250000000000000 : Rat)
  },
  {
    cells := [864, 609, 611, 865, 879, 880, 613, 856, 612, 608, 610, 615, 857, 614, 866, 867]
    lowerFloor := (103923979818553 / 40000000000000 : Rat)
    upperCeiling := (2598099515638991 / 1000000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1502, 1193, 1503]
    lowerFloor := (130877659400609 / 125000000000000 : Rat)
    upperCeiling := (261755322139921 / 250000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [63, 1941, 62]
    lowerFloor := (428839060479 / 500000000000000 : Rat)
    upperCeiling := (214771843237 / 250000000000000 : Rat)
  },
  {
    cells := [1308, 1309, 1350, 1351]
    lowerFloor := (1386293708877803 / 1000000000000000 : Rat)
    upperCeiling := (1386294414543671 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1685, 1752]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [319, 1588, 1589, 320]
    lowerFloor := (383210571615201 / 500000000000000 : Rat)
    upperCeiling := (95802778600153 / 125000000000000 : Rat)
  },
  {
    cells := [1624, 1813]
    lowerFloor := (138629305665441 / 200000000000000 : Rat)
    upperCeiling := (346573616986887 / 500000000000000 : Rat)
  },
  {
    cells := [319, 1134, 1426, 1427, 1135, 320]
    lowerFloor := (11004496165371 / 7812500000000 : Rat)
    upperCeiling := (3521438778263 / 2500000000000 : Rat)
  },
  {
    cells := [1573, 1833]
    lowerFloor := (693038349133689 / 1000000000000000 : Rat)
    upperCeiling := (693038882476449 / 1000000000000000 : Rat)
  },
  {
    cells := [1451, 1479, 1448]
    lowerFloor := (54909247676843 / 50000000000000 : Rat)
    upperCeiling := (549092476810997 / 500000000000000 : Rat)
  },
  {
    cells := [1214, 980, 1151, 1089, 983, 1215]
    lowerFloor := (177888121386473 / 100000000000000 : Rat)
    upperCeiling := (1778881216044773 / 1000000000000000 : Rat)
  },
  {
    cells := [1156, 1859, 1155]
    lowerFloor := (909082397188379 / 1000000000000000 : Rat)
    upperCeiling := (454541198739821 / 500000000000000 : Rat)
  },
  {
    cells := [329, 1575, 1578, 331]
    lowerFloor := (153817300112191 / 200000000000000 : Rat)
    upperCeiling := (384543788148723 / 500000000000000 : Rat)
  },
  {
    cells := [329, 1124, 1432, 1433, 1125, 331]
    lowerFloor := (44075447241769 / 31250000000000 : Rat)
    upperCeiling := (352603579285727 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [677, 1912, 678]
    lowerFloor := (63840745219419 / 200000000000000 : Rat)
    upperCeiling := (319204024323067 / 1000000000000000 : Rat)
  },
  {
    cells := [678, 1912, 677]
    lowerFloor := (63840745219419 / 200000000000000 : Rat)
    upperCeiling := (319204024323067 / 1000000000000000 : Rat)
  },
  {
    cells := [1811, 1626]
    lowerFloor := (69314652832583 / 100000000000000 : Rat)
    upperCeiling := (693147233973999 / 1000000000000000 : Rat)
  },
  {
    cells := [1634, 1803]
    lowerFloor := (86643316039711 / 125000000000000 : Rat)
    upperCeiling := (693147233975001 / 1000000000000000 : Rat)
  },
  {
    cells := [35, 1942, 36]
    lowerFloor := (722919198687 / 1000000000000000 : Rat)
    upperCeiling := (181082199101 / 250000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1457, 1459, 1458]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1458, 1459, 1457]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [665, 1918, 666]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [666, 1918, 665]
    lowerFloor := (63075485081363 / 200000000000000 : Rat)
    upperCeiling := (157688865932169 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1323, 1335, 1324, 1336]
    lowerFloor := (55451748354659 / 40000000000000 : Rat)
    upperCeiling := (693147207272553 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1660, 1777]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [814, 632, 633, 815, 925, 926, 632, 925, 634, 634, 635, 633, 926, 635, 812, 813]
    lowerFloor := (1301212448266251 / 500000000000000 : Rat)
    upperCeiling := (130121250915793 / 50000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1458, 1459, 1457]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [35, 1942, 36]
    lowerFloor := (722919198687 / 1000000000000000 : Rat)
    upperCeiling := (181082199101 / 250000000000000 : Rat)
  },
  {
    cells := [291, 1116, 293, 1035, 1037, 292, 1036, 1038, 1117, 294]
    lowerFloor := (1902709674450793 / 1000000000000000 : Rat)
    upperCeiling := (95135483787157 / 50000000000000 : Rat)
  },
  {
    cells := [678, 1912, 677]
    lowerFloor := (63840745219419 / 200000000000000 : Rat)
    upperCeiling := (319204024323067 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [35, 1942, 36]
    lowerFloor := (722919198687 / 1000000000000000 : Rat)
    upperCeiling := (181082199101 / 250000000000000 : Rat)
  },
  {
    cells := [1323, 1335, 1324, 1336]
    lowerFloor := (55451748354659 / 40000000000000 : Rat)
    upperCeiling := (693147207272553 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1660, 1777]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [814, 632, 633, 815, 925, 926, 632, 925, 634, 634, 635, 633, 926, 635, 812, 813]
    lowerFloor := (1301212448266251 / 500000000000000 : Rat)
    upperCeiling := (130121250915793 / 50000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1458, 1459, 1457]
    lowerFloor := (1098612288628763 / 1000000000000000 : Rat)
    upperCeiling := (274653072172459 / 250000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [35, 1942, 36]
    lowerFloor := (722919198687 / 1000000000000000 : Rat)
    upperCeiling := (181082199101 / 250000000000000 : Rat)
  },
  {
    cells := [291, 1116, 293, 1035, 1037, 292, 1036, 1038, 1117, 294]
    lowerFloor := (1902709674450793 / 1000000000000000 : Rat)
    upperCeiling := (95135483787157 / 50000000000000 : Rat)
  },
  {
    cells := [678, 1912, 677]
    lowerFloor := (63840745219419 / 200000000000000 : Rat)
    upperCeiling := (319204024323067 / 1000000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [35, 1942, 36]
    lowerFloor := (722919198687 / 1000000000000000 : Rat)
    upperCeiling := (181082199101 / 250000000000000 : Rat)
  },
  {
    cells := [327, 1580, 1581, 328]
    lowerFloor := (48065072295871 / 62500000000000 : Rat)
    upperCeiling := (384521116305943 / 500000000000000 : Rat)
  },
  {
    cells := [1154, 1860, 1153]
    lowerFloor := (181814171720629 / 200000000000000 : Rat)
    upperCeiling := (113633857361773 / 125000000000000 : Rat)
  },
  {
    cells := [327, 1435, 1126, 1127, 1434, 328]
    lowerFloor := (282074917259499 / 200000000000000 : Rat)
    upperCeiling := (352593647905563 / 250000000000000 : Rat)
  },
  {
    cells := [1453, 1470, 1454]
    lowerFloor := (34330598017717 / 31250000000000 : Rat)
    upperCeiling := (274644784157361 / 250000000000000 : Rat)
  },
  {
    cells := [1654, 1783]
    lowerFloor := (43321658019783 / 62500000000000 : Rat)
    upperCeiling := (693147233975101 / 1000000000000000 : Rat)
  },
  {
    cells := [1084, 1106, 1107, 1107, 1106, 1083]
    lowerFloor := (447906460190981 / 250000000000000 : Rat)
    upperCeiling := (895812920424863 / 500000000000000 : Rat)
  },
  {
    cells := [1720, 1717]
    lowerFloor := (21660829009889 / 31250000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [326, 1582, 1583, 325]
    lowerFloor := (38330770776847 / 50000000000000 : Rat)
    upperCeiling := (383308250153707 / 500000000000000 : Rat)
  },
  {
    cells := [326, 1422, 1138, 1137, 1423, 325]
    lowerFloor := (281754058161473 / 200000000000000 : Rat)
    upperCeiling := (704385146550209 / 500000000000000 : Rat)
  },
  {
    cells := [496, 1539, 1538, 497]
    lowerFloor := (26475773886617 / 31250000000000 : Rat)
    upperCeiling := (423612733192943 / 500000000000000 : Rat)
  },
  {
    cells := [497, 1538, 1539, 496]
    lowerFloor := (26475773886617 / 31250000000000 : Rat)
    upperCeiling := (423612733192943 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1120, 1862, 1121]
    lowerFloor := (109395606864449 / 125000000000000 : Rat)
    upperCeiling := (437582427486647 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1121, 1862, 1120]
    lowerFloor := (109395606864449 / 125000000000000 : Rat)
    upperCeiling := (437582427486647 / 500000000000000 : Rat)
  },
  {
    cells := [1821, 1616]
    lowerFloor := (693146528378379 / 1000000000000000 : Rat)
    upperCeiling := (86643404242717 / 125000000000000 : Rat)
  },
  {
    cells := [1613, 1822]
    lowerFloor := (693146528379241 / 1000000000000000 : Rat)
    upperCeiling := (693147233940257 / 1000000000000000 : Rat)
  },
  {
    cells := [599, 1922, 598]
    lowerFloor := (205582727938641 / 1000000000000000 : Rat)
    upperCeiling := (205583336996981 / 1000000000000000 : Rat)
  },
  {
    cells := [1749, 1688]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [595, 1924, 594]
    lowerFloor := (203837597144647 / 1000000000000000 : Rat)
    upperCeiling := (101919106023301 / 500000000000000 : Rat)
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [597, 1923, 596]
    lowerFloor := (203841167150707 / 1000000000000000 : Rat)
    upperCeiling := (8153671281627 / 40000000000000 : Rat)
  },
  {
    cells := [1657, 1780]
    lowerFloor := (346573264158239 / 500000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [1310, 1311, 1348, 1349]
    lowerFloor := (277258741774679 / 200000000000000 : Rat)
    upperCeiling := (346573603636089 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [177, 935, 1198, 1199, 175, 1200, 1201, 176, 934, 174]
    lowerFloor := (909383573282539 / 500000000000000 : Rat)
    upperCeiling := (363753440329831 / 200000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [599, 1922, 598]
    lowerFloor := (205582727938641 / 1000000000000000 : Rat)
    upperCeiling := (205583336996981 / 1000000000000000 : Rat)
  },
  {
    cells := [1319, 1321, 1338, 1340]
    lowerFloor := (1386293708866543 / 1000000000000000 : Rat)
    upperCeiling := (13862944145451 / 10000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1310, 1311, 1348, 1349]
    lowerFloor := (277258741774679 / 200000000000000 : Rat)
    upperCeiling := (346573603636089 / 250000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1658, 1779]
    lowerFloor := (693146528316477 / 1000000000000000 : Rat)
    upperCeiling := (138629446795021 / 200000000000000 : Rat)
  },
  {
    cells := [177, 935, 1198, 1199, 175, 1200, 1201, 176, 934, 174]
    lowerFloor := (909383573282539 / 500000000000000 : Rat)
    upperCeiling := (363753440329831 / 200000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [599, 1922, 598]
    lowerFloor := (205582727938641 / 1000000000000000 : Rat)
    upperCeiling := (205583336996981 / 1000000000000000 : Rat)
  },
  {
    cells := [1319, 1321, 1338, 1340]
    lowerFloor := (1386293708866543 / 1000000000000000 : Rat)
    upperCeiling := (13862944145451 / 10000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1687, 1750]
    lowerFloor := (346573264158237 / 500000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [945, 1870, 942]
    lowerFloor := (713045420127399 / 1000000000000000 : Rat)
    upperCeiling := (142609110795617 / 200000000000000 : Rat)
  },
  {
    cells := [1625, 1812]
    lowerFloor := (86643316040837 / 125000000000000 : Rat)
    upperCeiling := (693147233973859 / 1000000000000000 : Rat)
  },
  {
    cells := [945, 1484, 1485, 942]
    lowerFloor := (1241479911721799 / 1000000000000000 : Rat)
    upperCeiling := (310370011396933 / 250000000000000 : Rat)
  },
  {
    cells := [1700, 1737]
    lowerFloor := (346573264158227 / 500000000000000 : Rat)
    upperCeiling := (693147233975107 / 1000000000000000 : Rat)
  },
  {
    cells := [1708, 1729]
    lowerFloor := (693146528316451 / 1000000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [944, 1486, 1487, 943]
    lowerFloor := (620739849388459 / 500000000000000 : Rat)
    upperCeiling := (62073991632041 / 50000000000000 : Rat)
  },
  {
    cells := [1653, 1784]
    lowerFloor := (693146528316543 / 1000000000000000 : Rat)
    upperCeiling := (6931472339751 / 10000000000000 : Rat)
  },
  {
    cells := [1385, 1537, 1384]
    lowerFloor := (263059130182439 / 250000000000000 : Rat)
    upperCeiling := (1052236854125243 / 1000000000000000 : Rat)
  },
  {
    cells := [1385, 1282, 1282, 1384]
    lowerFloor := (1385563419267661 / 1000000000000000 : Rat)
    upperCeiling := (692781876336383 / 500000000000000 : Rat)
  },
  {
    cells := [1133, 1861, 1132]
    lowerFloor := (445448044788399 / 500000000000000 : Rat)
    upperCeiling := (178179217934809 / 200000000000000 : Rat)
  },
  {
    cells := [1132, 1861, 1133]
    lowerFloor := (445448044788399 / 500000000000000 : Rat)
    upperCeiling := (178179217934809 / 200000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1746, 1691]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1644, 1793]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1793, 1644]
    lowerFloor := (346573264158309 / 500000000000000 : Rat)
    upperCeiling := (346573616987547 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [607, 931, 1396, 1480, 1207, 652, 145, 37, 1]
    lowerFloor := (372632373702849 / 250000000000000 : Rat)
    upperCeiling := (298105905684507 / 200000000000000 : Rat)
  },
  {
    cells := [607, 931, 1396, 1480, 1207, 652, 145, 37, 1]
    lowerFloor := (372632373702849 / 250000000000000 : Rat)
    upperCeiling := (298105905684507 / 200000000000000 : Rat)
  },
  {
    cells := [0, 27, 105, 184, 431, 186, 104, 30, 1, 27, 106, 383, 714, 715, 385, 107, 29, 105, 383, 784, 958, 787, 384, 103, 184, 714, 958, 957, 713, 185, 431, 715, 787, 713, 430, 186, 385, 384, 185, 104, 107, 103, 30, 29, 1]
    lowerFloor := (2830098109351687 / 1000000000000000 : Rat)
    upperCeiling := (707524527711753 / 250000000000000 : Rat)
  },
  {
    cells := [606, 746, 729, 183, 68, 747, 1187, 1123, 483, 76, 728, 1122, 1077, 481, 75, 182, 482, 480, 134, 26, 69, 77, 74, 28, 0]
    lowerFloor := (281044346101159 / 125000000000000 : Rat)
    upperCeiling := (1124177415000891 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1223, 1840, 1224]
    lowerFloor := (60559301455851 / 62500000000000 : Rat)
    upperCeiling := (968948837343163 / 1000000000000000 : Rat)
  },
  {
    cells := [627, 1529, 1530, 626]
    lowerFloor := (903280359845747 / 1000000000000000 : Rat)
    upperCeiling := (451640421002423 / 500000000000000 : Rat)
  },
  {
    cells := [171, 970, 1865, 972, 170]
    lowerFloor := (394565704409721 / 500000000000000 : Rat)
    upperCeiling := (986414261817 / 1250000000000 : Rat)
  },
  {
    cells := [602, 1536, 1535, 603]
    lowerFloor := (436534250294129 / 500000000000000 : Rat)
    upperCeiling := (27283409188421 / 31250000000000 : Rat)
  },
  {
    cells := [1110, 1863, 1111]
    lowerFloor := (874682097185309 / 1000000000000000 : Rat)
    upperCeiling := (437341048621297 / 500000000000000 : Rat)
  },
  {
    cells := [1705, 1732]
    lowerFloor := (173286632079113 / 250000000000000 : Rat)
    upperCeiling := (173286808493777 / 250000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1221, 1841, 1222]
    lowerFloor := (242237204168137 / 250000000000000 : Rat)
    upperCeiling := (968948830722089 / 1000000000000000 : Rat)
  },
  {
    cells := [625, 1532, 1531, 624]
    lowerFloor := (903269495218279 / 1000000000000000 : Rat)
    upperCeiling := (451634988704829 / 500000000000000 : Rat)
  },
  {
    cells := [173, 971, 1864, 973, 172]
    lowerFloor := (789131503503059 / 1000000000000000 : Rat)
    upperCeiling := (770636234509 / 976562500000 : Rat)
  },
  {
    cells := [604, 1534, 1533, 605]
    lowerFloor := (13643487640539 / 15625000000000 : Rat)
    upperCeiling := (436591900986801 / 500000000000000 : Rat)
  },
  {
    cells := [1121, 1862, 1120]
    lowerFloor := (109395606864449 / 125000000000000 : Rat)
    upperCeiling := (437582427486647 / 500000000000000 : Rat)
  },
  {
    cells := [1691, 1746]
    lowerFloor := (86643316039559 / 125000000000000 : Rat)
    upperCeiling := (346573616987553 / 500000000000000 : Rat)
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1946]
    lowerFloor := 0
    upperCeiling := 0
  },
  {
    cells := [1655, 1782]
    lowerFloor := (346573264158249 / 500000000000000 : Rat)
    upperCeiling := (10830425530861 / 15625000000000 : Rat)
  },
  {
    cells := [1162, 1856, 1161]
    lowerFloor := (909197534272473 / 1000000000000000 : Rat)
    upperCeiling := (454598767282993 / 500000000000000 : Rat)
  },
  {
    cells := [437, 1568, 1567, 436]
    lowerFloor := (162945464135269 / 200000000000000 : Rat)
    upperCeiling := (101841021411221 / 125000000000000 : Rat)
  },
  {
    cells := [16, 786, 1884, 785, 17]
    lowerFloor := (256321803387909 / 500000000000000 : Rat)
    upperCeiling := (102528731667731 / 200000000000000 : Rat)
  },
  {
    cells := [139, 1596, 1595, 140]
    lowerFloor := (89037733847889 / 125000000000000 : Rat)
    upperCeiling := (712303210389909 / 1000000000000000 : Rat)
  },
  {
    cells := [25, 1945, 24]
    lowerFloor := (46993975011 / 125000000000000 : Rat)
    upperCeiling := (377362253977 / 1000000000000000 : Rat)
  },
]

def obligations : Array FloorBranch := #[
  {
    retainedFloor := 0
    constant := 0
    terms := []
  },
  {
    retainedFloor := 0
    constant := 0
    terms := []
  },
  {
    retainedFloor := 0
    constant := 0
    terms := []
  },
  {
    retainedFloor := 0
    constant := 0
    terms := [{ recordIndex := 1, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 2, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 3, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := 0
    constant := 0
    terms := [{ recordIndex := 4, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 5, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 6, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := 0
    constant := 0
    terms := [{ recordIndex := 7, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 8, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 9, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := 0
    constant := 0
    terms := [{ recordIndex := 10, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 11, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 12, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (159061351407 / 125000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 0, useUpper := false, coefficient := (790643 / 200000 : Rat) }]
  },
  {
    retainedFloor := (159061351407 / 125000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 0, useUpper := false, coefficient := (790643 / 200000 : Rat) }]
  },
  {
    retainedFloor := (159061351407 / 125000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 0, useUpper := false, coefficient := (790643 / 200000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 13, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 14, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 15, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 16, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 17, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 18, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 19, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 20, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 21, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 22, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 23, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 24, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (124674862521 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 25, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 26, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 27, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (15584433431 / 62500000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 28, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 29, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 30, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 31, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 32, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 33, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (153218520899 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 34, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 35, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 36, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 37, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 38, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 39, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 40, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 41, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 42, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 43, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 44, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 45, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (714172293549 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 46, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 47, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 48, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (623921224463 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 49, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 50, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 51, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (69028549851 / 100000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 52, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 53, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 54, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (172890319341 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 55, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 56, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 57, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 58, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 59, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 60, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := 0
    constant := 0
    terms := [{ recordIndex := 61, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 62, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 63, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 64, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 65, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 66, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (204710251747 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 67, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 68, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 69, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 70, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 71, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 72, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 73, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 74, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 75, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (23110935103 / 50000000000 : Rat)
    constant := (-86687123758692025543633665333622289454676823 / 125000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 106, useUpper := false, coefficient := (83299841176529 / 500000000000000 : Rat) }, { recordIndex := 107, useUpper := false, coefficient := (83299841176529 / 500000000000000 : Rat) }, { recordIndex := 108, useUpper := false, coefficient := (83299841176529 / 250000000000000 : Rat) }, { recordIndex := 109, useUpper := false, coefficient := (333400336186257 / 2000000000000000 : Rat) }, { recordIndex := 110, useUpper := false, coefficient := (333400336186257 / 2000000000000000 : Rat) }, { recordIndex := 111, useUpper := false, coefficient := (333400336186257 / 1000000000000000 : Rat) }, { recordIndex := 112, useUpper := false, coefficient := (333400299107627 / 2000000000000000 : Rat) }, { recordIndex := 113, useUpper := false, coefficient := (333400299107627 / 2000000000000000 : Rat) }, { recordIndex := 114, useUpper := false, coefficient := (333400299107627 / 1000000000000000 : Rat) }]
  },
  {
    retainedFloor := (23110935103 / 50000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 76, useUpper := false, coefficient := (83299841176529 / 500000000000000 : Rat) }, { recordIndex := 77, useUpper := true, coefficient := (-611971662515587252135813 / 500000000000000000000000000000 : Rat) }, { recordIndex := 78, useUpper := true, coefficient := (-83299229204866484412747864187 / 500000000000000000000000000000 : Rat) }, { recordIndex := 79, useUpper := true, coefficient := (-83299229204866484412747864187 / 500000000000000000000000000000 : Rat) }, { recordIndex := 80, useUpper := true, coefficient := (-611971662515587252135813 / 500000000000000000000000000000 : Rat) }, { recordIndex := 81, useUpper := false, coefficient := (333400336186257 / 2000000000000000 : Rat) }, { recordIndex := 82, useUpper := true, coefficient := (-166692963696868555408404417231 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 83, useUpper := true, coefficient := (-7204396259944591595582769 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 84, useUpper := true, coefficient := (-166692963696868555408404417231 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 85, useUpper := true, coefficient := (-7204396259944591595582769 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 86, useUpper := false, coefficient := (333400299107627 / 2000000000000000 : Rat) }, { recordIndex := 87, useUpper := true, coefficient := (-333385890104545949028838819281 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 88, useUpper := true, coefficient := (-14409003081050971161180719 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 89, useUpper := true, coefficient := (-333385890104545949028838819281 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 90, useUpper := true, coefficient := (-14409003081050971161180719 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 91, useUpper := false, coefficient := (83299841176529 / 500000000000000 : Rat) }, { recordIndex := 92, useUpper := true, coefficient := (-611971662515587252135813 / 500000000000000000000000000000 : Rat) }, { recordIndex := 93, useUpper := true, coefficient := (-83299229204866484412747864187 / 500000000000000000000000000000 : Rat) }, { recordIndex := 94, useUpper := true, coefficient := (-83299229204866484412747864187 / 500000000000000000000000000000 : Rat) }, { recordIndex := 95, useUpper := true, coefficient := (-611971662515587252135813 / 500000000000000000000000000000 : Rat) }, { recordIndex := 96, useUpper := false, coefficient := (333400336186257 / 2000000000000000 : Rat) }, { recordIndex := 97, useUpper := true, coefficient := (-166692963696868555408404417231 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 98, useUpper := true, coefficient := (-7204396259944591595582769 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 99, useUpper := true, coefficient := (-166692963696868555408404417231 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 100, useUpper := true, coefficient := (-7204396259944591595582769 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 101, useUpper := false, coefficient := (333400299107627 / 2000000000000000 : Rat) }, { recordIndex := 102, useUpper := true, coefficient := (-333385890104545949028838819281 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 103, useUpper := true, coefficient := (-14409003081050971161180719 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 104, useUpper := true, coefficient := (-333385890104545949028838819281 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 105, useUpper := true, coefficient := (-14409003081050971161180719 / 2000000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (830245891867 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 115, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 116, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 117, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (463273469617 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 118, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 119, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 120, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 121, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 122, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 123, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (62548801483 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 124, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 125, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 126, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 127, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 128, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 129, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 130, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 131, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 132, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (767762536091 / 1000000000000 : Rat)
    constant := (-123602758666655279162960534533065686161917247 / 90909090909091000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 171, useUpper := false, coefficient := (86974611 / 2000000000000002 : Rat) }, { recordIndex := 172, useUpper := false, coefficient := (86974611 / 2000000000000002 : Rat) }, { recordIndex := 173, useUpper := false, coefficient := (86974611 / 1000000000000001 : Rat) }, { recordIndex := 174, useUpper := false, coefficient := (39437682226443 / 142857142857143 : Rat) }, { recordIndex := 175, useUpper := false, coefficient := (39437682226443 / 142857142857143 : Rat) }, { recordIndex := 176, useUpper := false, coefficient := (78875364452886 / 142857142857143 : Rat) }, { recordIndex := 177, useUpper := false, coefficient := (223936180927594 / 1000000000000001 : Rat) }, { recordIndex := 178, useUpper := false, coefficient := (223936180927594 / 1000000000000001 : Rat) }, { recordIndex := 179, useUpper := false, coefficient := (447872361855188 / 1000000000000001 : Rat) }]
  },
  {
    retainedFloor := (767762536091 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 133, useUpper := false, coefficient := (86974611 / 2000000000000002 : Rat) }, { recordIndex := 134, useUpper := true, coefficient := (-6784683816571847645607 / 400000000000000400000000000000 : Rat) }, { recordIndex := 135, useUpper := true, coefficient := (-134573062971886397127 / 9478672985782000000000000000 : Rat) }, { recordIndex := 136, useUpper := true, coefficient := (-280184950341735590661 / 22727272727272750000000000000 : Rat) }, { recordIndex := 137, useUpper := true, coefficient := (-280184950341735590661 / 22727272727272750000000000000 : Rat) }, { recordIndex := 138, useUpper := true, coefficient := (-6784683816571847645607 / 400000000000000400000000000000 : Rat) }, { recordIndex := 139, useUpper := true, coefficient := (-134573062971886397127 / 9478672985782000000000000000 : Rat) }, { recordIndex := 140, useUpper := false, coefficient := (39437682226443 / 142857142857143 : Rat) }, { recordIndex := 141, useUpper := true, coefficient := (-14917502970029957944902405057 / 142857142857143000000000000000 : Rat) }, { recordIndex := 142, useUpper := true, coefficient := (-10145504529022034888027631 / 12987012987013000000000000000 : Rat) }, { recordIndex := 143, useUpper := true, coefficient := (-39326081676623757616231696059 / 142857142857143000000000000000 : Rat) }, { recordIndex := 144, useUpper := true, coefficient := (-24520179256413042055097594943 / 142857142857143000000000000000 : Rat) }, { recordIndex := 145, useUpper := false, coefficient := (223936180927594 / 1000000000000001 : Rat) }, { recordIndex := 146, useUpper := true, coefficient := (-2271224502382145067258379 / 31218781218781250000000000 : Rat) }, { recordIndex := 147, useUpper := true, coefficient := (-1447826995736759334857257347 / 9615384615384625000000000000 : Rat) }, { recordIndex := 148, useUpper := true, coefficient := (-76288763833269797553104973 / 125000000000000125000000000000 : Rat) }, { recordIndex := 149, useUpper := true, coefficient := (-2271224502382145067258379 / 31218781218781250000000000 : Rat) }, { recordIndex := 150, useUpper := true, coefficient := (-1447826995736759334857257347 / 9615384615384625000000000000 : Rat) }, { recordIndex := 151, useUpper := true, coefficient := (-76288763833269797553104973 / 125000000000000125000000000000 : Rat) }, { recordIndex := 152, useUpper := false, coefficient := (86974611 / 2000000000000002 : Rat) }, { recordIndex := 153, useUpper := true, coefficient := (-6784683816571847645607 / 400000000000000400000000000000 : Rat) }, { recordIndex := 154, useUpper := true, coefficient := (-280184950341735590661 / 22727272727272750000000000000 : Rat) }, { recordIndex := 155, useUpper := true, coefficient := (-134573062971886397127 / 9478672985782000000000000000 : Rat) }, { recordIndex := 156, useUpper := true, coefficient := (-280184950341735590661 / 22727272727272750000000000000 : Rat) }, { recordIndex := 157, useUpper := true, coefficient := (-6784683816571847645607 / 400000000000000400000000000000 : Rat) }, { recordIndex := 158, useUpper := true, coefficient := (-134573062971886397127 / 9478672985782000000000000000 : Rat) }, { recordIndex := 159, useUpper := false, coefficient := (39437682226443 / 142857142857143 : Rat) }, { recordIndex := 160, useUpper := true, coefficient := (-14917502970029957944902405057 / 142857142857143000000000000000 : Rat) }, { recordIndex := 161, useUpper := true, coefficient := (-10145504529022034888027631 / 12987012987013000000000000000 : Rat) }, { recordIndex := 162, useUpper := true, coefficient := (-39326081676623757616231696059 / 142857142857143000000000000000 : Rat) }, { recordIndex := 163, useUpper := true, coefficient := (-24520179256413042055097594943 / 142857142857143000000000000000 : Rat) }, { recordIndex := 164, useUpper := false, coefficient := (223936180927594 / 1000000000000001 : Rat) }, { recordIndex := 165, useUpper := true, coefficient := (-2271224502382145067258379 / 31218781218781250000000000 : Rat) }, { recordIndex := 166, useUpper := true, coefficient := (-1447826995736759334857257347 / 9615384615384625000000000000 : Rat) }, { recordIndex := 167, useUpper := true, coefficient := (-76288763833269797553104973 / 125000000000000125000000000000 : Rat) }, { recordIndex := 168, useUpper := true, coefficient := (-2271224502382145067258379 / 31218781218781250000000000 : Rat) }, { recordIndex := 169, useUpper := true, coefficient := (-1447826995736759334857257347 / 9615384615384625000000000000 : Rat) }, { recordIndex := 170, useUpper := true, coefficient := (-76288763833269797553104973 / 125000000000000125000000000000 : Rat) }]
  },
  {
    retainedFloor := (151710556003 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 180, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 181, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 182, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (466846473433 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 183, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 184, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 185, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 186, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 187, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 188, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (258884653493 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 189, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 190, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 191, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 192, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 193, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 194, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 195, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 196, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 197, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (684801869321 / 1000000000000 : Rat)
    constant := (-1175204244729131096540238347620867080325295581 / 1000000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 246, useUpper := false, coefficient := (556546331884981 / 2000000000000000 : Rat) }, { recordIndex := 247, useUpper := false, coefficient := (556546331884981 / 2000000000000000 : Rat) }, { recordIndex := 248, useUpper := false, coefficient := (556546331884981 / 1000000000000000 : Rat) }, { recordIndex := 249, useUpper := false, coefficient := (101583 / 15625000000000 : Rat) }, { recordIndex := 250, useUpper := false, coefficient := (101583 / 15625000000000 : Rat) }, { recordIndex := 251, useUpper := false, coefficient := (101583 / 7812500000000 : Rat) }, { recordIndex := 252, useUpper := false, coefficient := (88690731022479 / 400000000000000 : Rat) }, { recordIndex := 253, useUpper := false, coefficient := (88690731022479 / 400000000000000 : Rat) }, { recordIndex := 254, useUpper := false, coefficient := (88690731022479 / 200000000000000 : Rat) }]
  },
  {
    retainedFloor := (684801869321 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 198, useUpper := false, coefficient := (556546331884981 / 2000000000000000 : Rat) }, { recordIndex := 199, useUpper := true, coefficient := (-2166594440833043912325217 / 250000000000000000000000000000 : Rat) }, { recordIndex := 200, useUpper := true, coefficient := (-33739012298493434292622432431 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 201, useUpper := true, coefficient := (-237114028608228561306339953371 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 202, useUpper := true, coefficient := (-741145865800517222538831333 / 100000000000000000000000000000 : Rat) }, { recordIndex := 203, useUpper := true, coefficient := (-741145865800517222538831333 / 100000000000000000000000000000 : Rat) }, { recordIndex := 204, useUpper := true, coefficient := (-2166594440833043912325217 / 250000000000000000000000000000 : Rat) }, { recordIndex := 205, useUpper := true, coefficient := (-33739012298493434292622432431 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 206, useUpper := true, coefficient := (-237114028608228561306339953371 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 207, useUpper := false, coefficient := (101583 / 15625000000000 : Rat) }, { recordIndex := 208, useUpper := true, coefficient := (-1129560590310027849 / 781250000000000000000000000 : Rat) }, { recordIndex := 209, useUpper := true, coefficient := (-3719958684982191441 / 1953125000000000000000000000 : Rat) }, { recordIndex := 210, useUpper := true, coefficient := (-3719958684982191441 / 1953125000000000000000000000 : Rat) }, { recordIndex := 211, useUpper := true, coefficient := (-8977916315017808559 / 1953125000000000000000000000 : Rat) }, { recordIndex := 212, useUpper := true, coefficient := (-12308029678485477873 / 3906250000000000000000000000 : Rat) }, { recordIndex := 213, useUpper := false, coefficient := (88690731022479 / 400000000000000 : Rat) }, { recordIndex := 214, useUpper := true, coefficient := (-339817491756651960854733 / 50000000000000000000000000000 : Rat) }, { recordIndex := 215, useUpper := true, coefficient := (-1203989356301009174931722049 / 200000000000000000000000000000 : Rat) }, { recordIndex := 216, useUpper := true, coefficient := (-15262486382712003483553788303 / 80000000000000000000000000000 : Rat) }, { recordIndex := 217, useUpper := true, coefficient := (-9967601856382911016680776523 / 400000000000000000000000000000 : Rat) }, { recordIndex := 218, useUpper := true, coefficient := (-339817491756651960854733 / 50000000000000000000000000000 : Rat) }, { recordIndex := 219, useUpper := true, coefficient := (-1203989356301009174931722049 / 200000000000000000000000000000 : Rat) }, { recordIndex := 220, useUpper := true, coefficient := (-15262486382712003483553788303 / 80000000000000000000000000000 : Rat) }, { recordIndex := 221, useUpper := true, coefficient := (-9967601856382911016680776523 / 400000000000000000000000000000 : Rat) }, { recordIndex := 222, useUpper := false, coefficient := (556546331884981 / 2000000000000000 : Rat) }, { recordIndex := 223, useUpper := true, coefficient := (-2166594440833043912325217 / 250000000000000000000000000000 : Rat) }, { recordIndex := 224, useUpper := true, coefficient := (-741145865800517222538831333 / 100000000000000000000000000000 : Rat) }, { recordIndex := 225, useUpper := true, coefficient := (-33739012298493434292622432431 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 226, useUpper := true, coefficient := (-237114028608228561306339953371 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 227, useUpper := true, coefficient := (-741145865800517222538831333 / 100000000000000000000000000000 : Rat) }, { recordIndex := 228, useUpper := true, coefficient := (-2166594440833043912325217 / 250000000000000000000000000000 : Rat) }, { recordIndex := 229, useUpper := true, coefficient := (-33739012298493434292622432431 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 230, useUpper := true, coefficient := (-237114028608228561306339953371 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 231, useUpper := false, coefficient := (101583 / 15625000000000 : Rat) }, { recordIndex := 232, useUpper := true, coefficient := (-3719958684982191441 / 1953125000000000000000000000 : Rat) }, { recordIndex := 233, useUpper := true, coefficient := (-1129560590310027849 / 781250000000000000000000000 : Rat) }, { recordIndex := 234, useUpper := true, coefficient := (-3719958684982191441 / 1953125000000000000000000000 : Rat) }, { recordIndex := 235, useUpper := true, coefficient := (-8977916315017808559 / 1953125000000000000000000000 : Rat) }, { recordIndex := 236, useUpper := true, coefficient := (-12308029678485477873 / 3906250000000000000000000000 : Rat) }, { recordIndex := 237, useUpper := false, coefficient := (88690731022479 / 400000000000000 : Rat) }, { recordIndex := 238, useUpper := true, coefficient := (-1203989356301009174931722049 / 200000000000000000000000000000 : Rat) }, { recordIndex := 239, useUpper := true, coefficient := (-15262486382712003483553788303 / 80000000000000000000000000000 : Rat) }, { recordIndex := 240, useUpper := true, coefficient := (-9967601856382911016680776523 / 400000000000000000000000000000 : Rat) }, { recordIndex := 241, useUpper := true, coefficient := (-339817491756651960854733 / 50000000000000000000000000000 : Rat) }, { recordIndex := 242, useUpper := true, coefficient := (-339817491756651960854733 / 50000000000000000000000000000 : Rat) }, { recordIndex := 243, useUpper := true, coefficient := (-1203989356301009174931722049 / 200000000000000000000000000000 : Rat) }, { recordIndex := 244, useUpper := true, coefficient := (-15262486382712003483553788303 / 80000000000000000000000000000 : Rat) }, { recordIndex := 245, useUpper := true, coefficient := (-9967601856382911016680776523 / 400000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (260836709363 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 255, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 256, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 257, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (116650878059 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 258, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 259, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 260, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 261, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 262, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 263, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (75872078561 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 264, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 265, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 266, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 267, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 268, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 269, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 270, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 271, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 272, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (348750225241 / 500000000000 : Rat)
    constant := (-37668913839996903275977748910955831740951289 / 31250000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 321, useUpper := false, coefficient := (216780438279213 / 1000000000000000 : Rat) }, { recordIndex := 322, useUpper := false, coefficient := (216780438279213 / 1000000000000000 : Rat) }, { recordIndex := 323, useUpper := false, coefficient := (216780438279213 / 500000000000000 : Rat) }, { recordIndex := 324, useUpper := false, coefficient := (1258943 / 125000000000000 : Rat) }, { recordIndex := 325, useUpper := false, coefficient := (1258943 / 125000000000000 : Rat) }, { recordIndex := 326, useUpper := false, coefficient := (1258943 / 62500000000000 : Rat) }, { recordIndex := 327, useUpper := false, coefficient := (283219551649243 / 1000000000000000 : Rat) }, { recordIndex := 328, useUpper := false, coefficient := (283219551649243 / 1000000000000000 : Rat) }, { recordIndex := 329, useUpper := false, coefficient := (283219551649243 / 500000000000000 : Rat) }]
  },
  {
    retainedFloor := (348750225241 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 273, useUpper := false, coefficient := (216780438279213 / 1000000000000000 : Rat) }, { recordIndex := 274, useUpper := true, coefficient := (-1060334837056214852400949833 / 200000000000000000000000000000 : Rat) }, { recordIndex := 275, useUpper := true, coefficient := (-45613383304499144484116211531 / 250000000000000000000000000000 : Rat) }, { recordIndex := 276, useUpper := true, coefficient := (-14436032626715383267666989417 / 500000000000000000000000000000 : Rat) }, { recordIndex := 277, useUpper := true, coefficient := (-153165622504581266196425877 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 278, useUpper := true, coefficient := (-153165622504581266196425877 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 279, useUpper := true, coefficient := (-1060334837056214852400949833 / 200000000000000000000000000000 : Rat) }, { recordIndex := 280, useUpper := true, coefficient := (-45613383304499144484116211531 / 250000000000000000000000000000 : Rat) }, { recordIndex := 281, useUpper := true, coefficient := (-14436032626715383267666989417 / 500000000000000000000000000000 : Rat) }, { recordIndex := 282, useUpper := false, coefficient := (1258943 / 125000000000000 : Rat) }, { recordIndex := 283, useUpper := true, coefficient := (-145756423180415002711 / 125000000000000000000000000000 : Rat) }, { recordIndex := 284, useUpper := true, coefficient := (-44607133721642259313 / 31250000000000000000000000000 : Rat) }, { recordIndex := 285, useUpper := true, coefficient := (-145756423180415002711 / 125000000000000000000000000000 : Rat) }, { recordIndex := 286, useUpper := true, coefficient := (-1113186576819584997289 / 125000000000000000000000000000 : Rat) }, { recordIndex := 287, useUpper := true, coefficient := (-934758041933015960037 / 125000000000000000000000000000 : Rat) }, { recordIndex := 288, useUpper := false, coefficient := (283219551649243 / 1000000000000000 : Rat) }, { recordIndex := 289, useUpper := true, coefficient := (-171786088879707502358584569 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 290, useUpper := true, coefficient := (-3732042065115483348086148951 / 500000000000000000000000000000 : Rat) }, { recordIndex := 291, useUpper := true, coefficient := (-469560383605220803762281811 / 12500000000000000000000000000 : Rat) }, { recordIndex := 292, useUpper := true, coefficient := (-238018850741714661500486572649 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 293, useUpper := true, coefficient := (-3732042065115483348086148951 / 500000000000000000000000000000 : Rat) }, { recordIndex := 294, useUpper := true, coefficient := (-171786088879707502358584569 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 295, useUpper := true, coefficient := (-469560383605220803762281811 / 12500000000000000000000000000 : Rat) }, { recordIndex := 296, useUpper := true, coefficient := (-238018850741714661500486572649 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 297, useUpper := false, coefficient := (216780438279213 / 1000000000000000 : Rat) }, { recordIndex := 298, useUpper := true, coefficient := (-153165622504581266196425877 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 299, useUpper := true, coefficient := (-1060334837056214852400949833 / 200000000000000000000000000000 : Rat) }, { recordIndex := 300, useUpper := true, coefficient := (-45613383304499144484116211531 / 250000000000000000000000000000 : Rat) }, { recordIndex := 301, useUpper := true, coefficient := (-14436032626715383267666989417 / 500000000000000000000000000000 : Rat) }, { recordIndex := 302, useUpper := true, coefficient := (-153165622504581266196425877 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 303, useUpper := true, coefficient := (-1060334837056214852400949833 / 200000000000000000000000000000 : Rat) }, { recordIndex := 304, useUpper := true, coefficient := (-45613383304499144484116211531 / 250000000000000000000000000000 : Rat) }, { recordIndex := 305, useUpper := true, coefficient := (-14436032626715383267666989417 / 500000000000000000000000000000 : Rat) }, { recordIndex := 306, useUpper := false, coefficient := (1258943 / 125000000000000 : Rat) }, { recordIndex := 307, useUpper := true, coefficient := (-44607133721642259313 / 31250000000000000000000000000 : Rat) }, { recordIndex := 308, useUpper := true, coefficient := (-145756423180415002711 / 125000000000000000000000000000 : Rat) }, { recordIndex := 309, useUpper := true, coefficient := (-145756423180415002711 / 125000000000000000000000000000 : Rat) }, { recordIndex := 310, useUpper := true, coefficient := (-1113186576819584997289 / 125000000000000000000000000000 : Rat) }, { recordIndex := 311, useUpper := true, coefficient := (-934758041933015960037 / 125000000000000000000000000000 : Rat) }, { recordIndex := 312, useUpper := false, coefficient := (283219551649243 / 1000000000000000 : Rat) }, { recordIndex := 313, useUpper := true, coefficient := (-171786088879707502358584569 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 314, useUpper := true, coefficient := (-469560383605220803762281811 / 12500000000000000000000000000 : Rat) }, { recordIndex := 315, useUpper := true, coefficient := (-238018850741714661500486572649 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 316, useUpper := true, coefficient := (-3732042065115483348086148951 / 500000000000000000000000000000 : Rat) }, { recordIndex := 317, useUpper := true, coefficient := (-3732042065115483348086148951 / 500000000000000000000000000000 : Rat) }, { recordIndex := 318, useUpper := true, coefficient := (-171786088879707502358584569 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 319, useUpper := true, coefficient := (-469560383605220803762281811 / 12500000000000000000000000000 : Rat) }, { recordIndex := 320, useUpper := true, coefficient := (-238018850741714661500486572649 / 1000000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (252362001183 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 330, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 331, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 332, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (462400928451 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 333, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 334, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 335, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 336, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 337, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 338, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (165747649161 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 339, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 340, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 341, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 342, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 343, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 344, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 345, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 346, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 347, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (158056323741 / 200000000000 : Rat)
    constant := (-58734949172518310835531372282093007513382501 / 41666666666666625000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 386, useUpper := false, coefficient := (74458678965224 / 333333333333333 : Rat) }, { recordIndex := 387, useUpper := false, coefficient := (74458678965224 / 333333333333333 : Rat) }, { recordIndex := 388, useUpper := false, coefficient := (148917357930448 / 333333333333333 : Rat) }, { recordIndex := 389, useUpper := false, coefficient := (92207968477252 / 333333333333333 : Rat) }, { recordIndex := 390, useUpper := false, coefficient := (92207968477252 / 333333333333333 : Rat) }, { recordIndex := 391, useUpper := false, coefficient := (184415936954504 / 333333333333333 : Rat) }, { recordIndex := 392, useUpper := false, coefficient := (12816127 / 222222222222222 : Rat) }, { recordIndex := 393, useUpper := false, coefficient := (12816127 / 222222222222222 : Rat) }, { recordIndex := 394, useUpper := false, coefficient := (12816127 / 111111111111111 : Rat) }]
  },
  {
    retainedFloor := (158056323741 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 348, useUpper := false, coefficient := (74458678965224 / 333333333333333 : Rat) }, { recordIndex := 349, useUpper := true, coefficient := (-217977240249371300687042423 / 2777777777777775000000000000 : Rat) }, { recordIndex := 350, useUpper := true, coefficient := (-656455990454776654636773697 / 4629629629629625000000000000 : Rat) }, { recordIndex := 351, useUpper := true, coefficient := (-64786176409720298981700191 / 20833333333333312500000000000 : Rat) }, { recordIndex := 352, useUpper := true, coefficient := (-217977240249371300687042423 / 2777777777777775000000000000 : Rat) }, { recordIndex := 353, useUpper := true, coefficient := (-656455990454776654636773697 / 4629629629629625000000000000 : Rat) }, { recordIndex := 354, useUpper := true, coefficient := (-64786176409720298981700191 / 20833333333333312500000000000 : Rat) }, { recordIndex := 355, useUpper := false, coefficient := (92207968477252 / 333333333333333 : Rat) }, { recordIndex := 356, useUpper := true, coefficient := (-448720490876397382632780753 / 4629629629629625000000000000 : Rat) }, { recordIndex := 357, useUpper := true, coefficient := (-335122378282540278152368463 / 83333333333333250000000000000 : Rat) }, { recordIndex := 358, useUpper := true, coefficient := (-22716869741030459721847631537 / 83333333333333250000000000000 : Rat) }, { recordIndex := 359, useUpper := true, coefficient := (-7487511641768923556304973223 / 41666666666666625000000000000 : Rat) }, { recordIndex := 360, useUpper := false, coefficient := (12816127 / 222222222222222 : Rat) }, { recordIndex := 361, useUpper := true, coefficient := (-4962619873965496795021 / 222222222222222000000000000000 : Rat) }, { recordIndex := 362, useUpper := true, coefficient := (-681473484723417896483 / 44444444444444400000000000000 : Rat) }, { recordIndex := 363, useUpper := true, coefficient := (-1111534925604353430641 / 55555555555555500000000000000 : Rat) }, { recordIndex := 364, useUpper := true, coefficient := (-681473484723417896483 / 44444444444444400000000000000 : Rat) }, { recordIndex := 365, useUpper := true, coefficient := (-4962619873965496795021 / 222222222222222000000000000000 : Rat) }, { recordIndex := 366, useUpper := true, coefficient := (-1111534925604353430641 / 55555555555555500000000000000 : Rat) }, { recordIndex := 367, useUpper := false, coefficient := (74458678965224 / 333333333333333 : Rat) }, { recordIndex := 368, useUpper := true, coefficient := (-217977240249371300687042423 / 2777777777777775000000000000 : Rat) }, { recordIndex := 369, useUpper := true, coefficient := (-656455990454776654636773697 / 4629629629629625000000000000 : Rat) }, { recordIndex := 370, useUpper := true, coefficient := (-64786176409720298981700191 / 20833333333333312500000000000 : Rat) }, { recordIndex := 371, useUpper := true, coefficient := (-217977240249371300687042423 / 2777777777777775000000000000 : Rat) }, { recordIndex := 372, useUpper := true, coefficient := (-656455990454776654636773697 / 4629629629629625000000000000 : Rat) }, { recordIndex := 373, useUpper := true, coefficient := (-64786176409720298981700191 / 20833333333333312500000000000 : Rat) }, { recordIndex := 374, useUpper := false, coefficient := (92207968477252 / 333333333333333 : Rat) }, { recordIndex := 375, useUpper := true, coefficient := (-448720490876397382632780753 / 4629629629629625000000000000 : Rat) }, { recordIndex := 376, useUpper := true, coefficient := (-335122378282540278152368463 / 83333333333333250000000000000 : Rat) }, { recordIndex := 377, useUpper := true, coefficient := (-22716869741030459721847631537 / 83333333333333250000000000000 : Rat) }, { recordIndex := 378, useUpper := true, coefficient := (-7487511641768923556304973223 / 41666666666666625000000000000 : Rat) }, { recordIndex := 379, useUpper := false, coefficient := (12816127 / 222222222222222 : Rat) }, { recordIndex := 380, useUpper := true, coefficient := (-4962619873965496795021 / 222222222222222000000000000000 : Rat) }, { recordIndex := 381, useUpper := true, coefficient := (-1111534925604353430641 / 55555555555555500000000000000 : Rat) }, { recordIndex := 382, useUpper := true, coefficient := (-681473484723417896483 / 44444444444444400000000000000 : Rat) }, { recordIndex := 383, useUpper := true, coefficient := (-681473484723417896483 / 44444444444444400000000000000 : Rat) }, { recordIndex := 384, useUpper := true, coefficient := (-4962619873965496795021 / 222222222222222000000000000000 : Rat) }, { recordIndex := 385, useUpper := true, coefficient := (-1111534925604353430641 / 55555555555555500000000000000 : Rat) }]
  },
  {
    retainedFloor := (8292358401 / 15625000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 395, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 396, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 397, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 398, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 399, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 400, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 401, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 402, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 403, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (349889289431 / 500000000000 : Rat)
    constant := (-310369644344392995883447797346243803798054987 / 250000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 434, useUpper := false, coefficient := (166665802547817 / 500000000000000 : Rat) }, { recordIndex := 435, useUpper := false, coefficient := (166665802547817 / 500000000000000 : Rat) }, { recordIndex := 436, useUpper := false, coefficient := (166665802547817 / 250000000000000 : Rat) }, { recordIndex := 437, useUpper := false, coefficient := 0 }, { recordIndex := 438, useUpper := false, coefficient := 0 }, { recordIndex := 439, useUpper := false, coefficient := 0 }, { recordIndex := 440, useUpper := false, coefficient := (83334197452183 / 500000000000000 : Rat) }, { recordIndex := 441, useUpper := false, coefficient := (83334197452183 / 500000000000000 : Rat) }, { recordIndex := 442, useUpper := false, coefficient := (83334197452183 / 250000000000000 : Rat) }]
  },
  {
    retainedFloor := (349889289431 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 404, useUpper := false, coefficient := (166665802547817 / 500000000000000 : Rat) }, { recordIndex := 405, useUpper := true, coefficient := (-62041591038315892057202799 / 244140625000000000000000000 : Rat) }, { recordIndex := 406, useUpper := true, coefficient := (-19338195361985377474047201 / 244140625000000000000000000 : Rat) }, { recordIndex := 407, useUpper := true, coefficient := (-62041591038315892057202799 / 244140625000000000000000000 : Rat) }, { recordIndex := 408, useUpper := true, coefficient := (-19338195361985377474047201 / 244140625000000000000000000 : Rat) }, { recordIndex := 409, useUpper := false, coefficient := 0 }, { recordIndex := 410, useUpper := true, coefficient := 0 }, { recordIndex := 411, useUpper := true, coefficient := 0 }, { recordIndex := 412, useUpper := true, coefficient := 0 }, { recordIndex := 413, useUpper := true, coefficient := 0 }, { recordIndex := 414, useUpper := false, coefficient := (83334197452183 / 500000000000000 : Rat) }, { recordIndex := 415, useUpper := true, coefficient := (-1980260594707410353751468333 / 50000000000000000000000000000 : Rat) }, { recordIndex := 416, useUpper := true, coefficient := (-6353159150510889646248531667 / 50000000000000000000000000000 : Rat) }, { recordIndex := 417, useUpper := true, coefficient := (-6353159150510889646248531667 / 50000000000000000000000000000 : Rat) }, { recordIndex := 418, useUpper := true, coefficient := (-1980260594707410353751468333 / 50000000000000000000000000000 : Rat) }, { recordIndex := 419, useUpper := false, coefficient := (166665802547817 / 500000000000000 : Rat) }, { recordIndex := 420, useUpper := true, coefficient := (-62041591038315892057202799 / 244140625000000000000000000 : Rat) }, { recordIndex := 421, useUpper := true, coefficient := (-19338195361985377474047201 / 244140625000000000000000000 : Rat) }, { recordIndex := 422, useUpper := true, coefficient := (-62041591038315892057202799 / 244140625000000000000000000 : Rat) }, { recordIndex := 423, useUpper := true, coefficient := (-19338195361985377474047201 / 244140625000000000000000000 : Rat) }, { recordIndex := 424, useUpper := false, coefficient := 0 }, { recordIndex := 425, useUpper := true, coefficient := 0 }, { recordIndex := 426, useUpper := true, coefficient := 0 }, { recordIndex := 427, useUpper := true, coefficient := 0 }, { recordIndex := 428, useUpper := true, coefficient := 0 }, { recordIndex := 429, useUpper := false, coefficient := (83334197452183 / 500000000000000 : Rat) }, { recordIndex := 430, useUpper := true, coefficient := (-1980260594707410353751468333 / 50000000000000000000000000000 : Rat) }, { recordIndex := 431, useUpper := true, coefficient := (-6353159150510889646248531667 / 50000000000000000000000000000 : Rat) }, { recordIndex := 432, useUpper := true, coefficient := (-6353159150510889646248531667 / 50000000000000000000000000000 : Rat) }, { recordIndex := 433, useUpper := true, coefficient := (-1980260594707410353751468333 / 50000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 443, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 444, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 445, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (38304629963 / 50000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 446, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 447, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 448, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (62548800629 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 449, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 450, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 451, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (57919163093 / 125000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 452, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 453, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 454, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 455, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 456, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 457, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (83015965801 / 100000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 458, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 459, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 460, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 461, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 462, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 463, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 464, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 465, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 466, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (767761197819 / 1000000000000 : Rat)
    constant := (-135962891295246832783201034951268170339739323 / 100000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 505, useUpper := false, coefficient := (4355209 / 100000000000000 : Rat) }, { recordIndex := 506, useUpper := false, coefficient := (4355209 / 100000000000000 : Rat) }, { recordIndex := 507, useUpper := false, coefficient := (4355209 / 50000000000000 : Rat) }, { recordIndex := 508, useUpper := false, coefficient := (447883575570391 / 2000000000000000 : Rat) }, { recordIndex := 509, useUpper := false, coefficient := (447883575570391 / 2000000000000000 : Rat) }, { recordIndex := 510, useUpper := false, coefficient := (447883575570391 / 1000000000000000 : Rat) }, { recordIndex := 511, useUpper := false, coefficient := (552116337325429 / 2000000000000000 : Rat) }, { recordIndex := 512, useUpper := false, coefficient := (552116337325429 / 2000000000000000 : Rat) }, { recordIndex := 513, useUpper := false, coefficient := (552116337325429 / 1000000000000000 : Rat) }]
  },
  {
    retainedFloor := (767761197819 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 467, useUpper := false, coefficient := (4355209 / 100000000000000 : Rat) }, { recordIndex := 468, useUpper := true, coefficient := (-851362327554047042327 / 50000000000000000000000000000 : Rat) }, { recordIndex := 469, useUpper := true, coefficient := (-1234057195934052749009 / 100000000000000000000000000000 : Rat) }, { recordIndex := 470, useUpper := true, coefficient := (-1418427148957853166337 / 100000000000000000000000000000 : Rat) }, { recordIndex := 471, useUpper := true, coefficient := (-1234057195934052749009 / 100000000000000000000000000000 : Rat) }, { recordIndex := 472, useUpper := true, coefficient := (-851362327554047042327 / 50000000000000000000000000000 : Rat) }, { recordIndex := 473, useUpper := true, coefficient := (-1418427148957853166337 / 100000000000000000000000000000 : Rat) }, { recordIndex := 474, useUpper := false, coefficient := (447883575570391 / 2000000000000000 : Rat) }, { recordIndex := 475, useUpper := true, coefficient := (-145505057768762484603445393707 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 476, useUpper := true, coefficient := (-301157705161433275859274649027 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 477, useUpper := true, coefficient := (-610406320097619768639978633 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 478, useUpper := true, coefficient := (-145505057768762484603445393707 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 479, useUpper := true, coefficient := (-301157705161433275859274649027 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 480, useUpper := true, coefficient := (-610406320097619768639978633 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 481, useUpper := false, coefficient := (552116337325429 / 2000000000000000 : Rat) }, { recordIndex := 482, useUpper := true, coefficient := (-1631559568711823279311109577 / 15625000000000000000000000000 : Rat) }, { recordIndex := 483, useUpper := true, coefficient := (-312486587295841911865677893 / 400000000000000000000000000000 : Rat) }, { recordIndex := 484, useUpper := true, coefficient := (-110110780877789958088134322107 / 400000000000000000000000000000 : Rat) }, { recordIndex := 485, useUpper := true, coefficient := (-2681849316643090783188890423 / 15625000000000000000000000000 : Rat) }, { recordIndex := 486, useUpper := false, coefficient := (4355209 / 100000000000000 : Rat) }, { recordIndex := 487, useUpper := true, coefficient := (-851362327554047042327 / 50000000000000000000000000000 : Rat) }, { recordIndex := 488, useUpper := true, coefficient := (-1418427148957853166337 / 100000000000000000000000000000 : Rat) }, { recordIndex := 489, useUpper := true, coefficient := (-1234057195934052749009 / 100000000000000000000000000000 : Rat) }, { recordIndex := 490, useUpper := true, coefficient := (-1234057195934052749009 / 100000000000000000000000000000 : Rat) }, { recordIndex := 491, useUpper := true, coefficient := (-851362327554047042327 / 50000000000000000000000000000 : Rat) }, { recordIndex := 492, useUpper := true, coefficient := (-1418427148957853166337 / 100000000000000000000000000000 : Rat) }, { recordIndex := 493, useUpper := false, coefficient := (447883575570391 / 2000000000000000 : Rat) }, { recordIndex := 494, useUpper := true, coefficient := (-145505057768762484603445393707 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 495, useUpper := true, coefficient := (-301157705161433275859274649027 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 496, useUpper := true, coefficient := (-610406320097619768639978633 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 497, useUpper := true, coefficient := (-145505057768762484603445393707 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 498, useUpper := true, coefficient := (-301157705161433275859274649027 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 499, useUpper := true, coefficient := (-610406320097619768639978633 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 500, useUpper := false, coefficient := (552116337325429 / 2000000000000000 : Rat) }, { recordIndex := 501, useUpper := true, coefficient := (-1631559568711823279311109577 / 15625000000000000000000000000 : Rat) }, { recordIndex := 502, useUpper := true, coefficient := (-312486587295841911865677893 / 400000000000000000000000000000 : Rat) }, { recordIndex := 503, useUpper := true, coefficient := (-110110780877789958088134322107 / 400000000000000000000000000000 : Rat) }, { recordIndex := 504, useUpper := true, coefficient := (-2681849316643090783188890423 / 15625000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (279926787517 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 514, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 515, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 516, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (484922135649 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 517, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 518, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 519, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 520, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 521, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 522, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (335166589053 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 523, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 524, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 525, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 526, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 527, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 528, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 529, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 530, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 531, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (9777301553 / 12500000000 : Rat)
    constant := (-341412405671778446851389494876356174559558277 / 250000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 582, useUpper := false, coefficient := (358616051258041 / 2000000000000000 : Rat) }, { recordIndex := 583, useUpper := false, coefficient := (358616051258041 / 2000000000000000 : Rat) }, { recordIndex := 584, useUpper := false, coefficient := (358616051258041 / 1000000000000000 : Rat) }, { recordIndex := 585, useUpper := false, coefficient := (160345985156189 / 500000000000000 : Rat) }, { recordIndex := 586, useUpper := false, coefficient := (160345985156189 / 500000000000000 : Rat) }, { recordIndex := 587, useUpper := false, coefficient := (160345985156189 / 250000000000000 : Rat) }, { recordIndex := 588, useUpper := false, coefficient := (8117203 / 2000000000000000 : Rat) }, { recordIndex := 589, useUpper := false, coefficient := (8117203 / 2000000000000000 : Rat) }, { recordIndex := 590, useUpper := false, coefficient := (8117203 / 1000000000000000 : Rat) }]
  },
  {
    retainedFloor := (9777301553 / 12500000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 532, useUpper := false, coefficient := (358616051258041 / 2000000000000000 : Rat) }, { recordIndex := 533, useUpper := true, coefficient := (-11158407596509743187013137 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 534, useUpper := true, coefficient := (-6572694053109467776429827461 / 500000000000000000000000000000 : Rat) }, { recordIndex := 535, useUpper := true, coefficient := (-26273605483985594263232314161 / 500000000000000000000000000000 : Rat) }, { recordIndex := 536, useUpper := true, coefficient := (-13145385991070982868576903437 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 537, useUpper := true, coefficient := (-26273605483985594263232314161 / 500000000000000000000000000000 : Rat) }, { recordIndex := 538, useUpper := true, coefficient := (-11158407596509743187013137 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 539, useUpper := true, coefficient := (-26290774097289918421436558359 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 540, useUpper := true, coefficient := (-200928922719922276361010613501 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 541, useUpper := false, coefficient := (160345985156189 / 500000000000000 : Rat) }, { recordIndex := 542, useUpper := true, coefficient := (-23517963326909769155035784193 / 250000000000000000000000000000 : Rat) }, { recordIndex := 543, useUpper := true, coefficient := (-5885513341665570362328843873 / 250000000000000000000000000000 : Rat) }, { recordIndex := 544, useUpper := true, coefficient := (-2435756514694754956733021 / 250000000000000000000000000000 : Rat) }, { recordIndex := 545, useUpper := true, coefficient := (-2435756514694754956733021 / 250000000000000000000000000000 : Rat) }, { recordIndex := 546, useUpper := true, coefficient := (-465056698155544508881765807 / 4000000000000000000000000000 : Rat) }, { recordIndex := 547, useUpper := true, coefficient := (-9632351303205097651753696421 / 25000000000000000000000000000 : Rat) }, { recordIndex := 548, useUpper := true, coefficient := (-11096160615623525300149157489 / 500000000000000000000000000000 : Rat) }, { recordIndex := 549, useUpper := false, coefficient := (8117203 / 2000000000000000 : Rat) }, { recordIndex := 550, useUpper := true, coefficient := (-44548803289927155897 / 40000000000000000000000000000 : Rat) }, { recordIndex := 551, useUpper := true, coefficient := (-190485658145445163353 / 250000000000000000000000000000 : Rat) }, { recordIndex := 552, useUpper := true, coefficient := (-352746510839881785549 / 400000000000000000000000000000 : Rat) }, { recordIndex := 553, useUpper := true, coefficient := (-44548803289927155897 / 40000000000000000000000000000 : Rat) }, { recordIndex := 554, useUpper := true, coefficient := (-3285186144951908162099 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 555, useUpper := true, coefficient := (-3445420826904059158357 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 556, useUpper := true, coefficient := (-70452035191533874211 / 80000000000000000000000000000 : Rat) }, { recordIndex := 557, useUpper := false, coefficient := (358616051258041 / 2000000000000000 : Rat) }, { recordIndex := 558, useUpper := true, coefficient := (-11158407596509743187013137 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 559, useUpper := true, coefficient := (-13145385991070982868576903437 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 560, useUpper := true, coefficient := (-26273605483985594263232314161 / 500000000000000000000000000000 : Rat) }, { recordIndex := 561, useUpper := true, coefficient := (-6572694053109467776429827461 / 500000000000000000000000000000 : Rat) }, { recordIndex := 562, useUpper := true, coefficient := (-26273605483985594263232314161 / 500000000000000000000000000000 : Rat) }, { recordIndex := 563, useUpper := true, coefficient := (-11158407596509743187013137 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 564, useUpper := true, coefficient := (-26290774097289918421436558359 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 565, useUpper := true, coefficient := (-200928922719922276361010613501 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 566, useUpper := false, coefficient := (160345985156189 / 500000000000000 : Rat) }, { recordIndex := 567, useUpper := true, coefficient := (-2435756514694754956733021 / 250000000000000000000000000000 : Rat) }, { recordIndex := 568, useUpper := true, coefficient := (-23517963326909769155035784193 / 250000000000000000000000000000 : Rat) }, { recordIndex := 569, useUpper := true, coefficient := (-5885513341665570362328843873 / 250000000000000000000000000000 : Rat) }, { recordIndex := 570, useUpper := true, coefficient := (-2435756514694754956733021 / 250000000000000000000000000000 : Rat) }, { recordIndex := 571, useUpper := true, coefficient := (-465056698155544508881765807 / 4000000000000000000000000000 : Rat) }, { recordIndex := 572, useUpper := true, coefficient := (-9632351303205097651753696421 / 25000000000000000000000000000 : Rat) }, { recordIndex := 573, useUpper := true, coefficient := (-11096160615623525300149157489 / 500000000000000000000000000000 : Rat) }, { recordIndex := 574, useUpper := false, coefficient := (8117203 / 2000000000000000 : Rat) }, { recordIndex := 575, useUpper := true, coefficient := (-190485658145445163353 / 250000000000000000000000000000 : Rat) }, { recordIndex := 576, useUpper := true, coefficient := (-352746510839881785549 / 400000000000000000000000000000 : Rat) }, { recordIndex := 577, useUpper := true, coefficient := (-44548803289927155897 / 40000000000000000000000000000 : Rat) }, { recordIndex := 578, useUpper := true, coefficient := (-44548803289927155897 / 40000000000000000000000000000 : Rat) }, { recordIndex := 579, useUpper := true, coefficient := (-3285186144951908162099 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 580, useUpper := true, coefficient := (-3445420826904059158357 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 581, useUpper := true, coefficient := (-70452035191533874211 / 80000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (81203403609 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 591, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 592, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 593, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (486755618999 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 594, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 595, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 596, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 597, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 598, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 599, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (171608693529 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 600, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 601, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 602, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 603, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 604, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 605, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 606, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 607, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 608, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (13319891429 / 15625000000 : Rat)
    constant := (-385100746711132519469211216918750350203949197 / 250000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 661, useUpper := false, coefficient := (395432343788877 / 1000000000000000 : Rat) }, { recordIndex := 662, useUpper := false, coefficient := (395432343788877 / 1000000000000000 : Rat) }, { recordIndex := 663, useUpper := false, coefficient := (395432343788877 / 500000000000000 : Rat) }, { recordIndex := 664, useUpper := false, coefficient := (209135311860531 / 2000000000000000 : Rat) }, { recordIndex := 665, useUpper := false, coefficient := (209135311860531 / 2000000000000000 : Rat) }, { recordIndex := 666, useUpper := false, coefficient := (209135311860531 / 1000000000000000 : Rat) }, { recordIndex := 667, useUpper := false, coefficient := (112343 / 400000000000000 : Rat) }, { recordIndex := 668, useUpper := false, coefficient := (112343 / 400000000000000 : Rat) }, { recordIndex := 669, useUpper := false, coefficient := (112343 / 200000000000000 : Rat) }]
  },
  {
    retainedFloor := (13319891429 / 15625000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 609, useUpper := false, coefficient := (395432343788877 / 1000000000000000 : Rat) }, { recordIndex := 610, useUpper := true, coefficient := (-4572234761763859917472089459 / 500000000000000000000000000000 : Rat) }, { recordIndex := 611, useUpper := true, coefficient := (-126109529922230409632405755959 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 612, useUpper := true, coefficient := (-2286119774125271968481307231 / 250000000000000000000000000000 : Rat) }, { recordIndex := 613, useUpper := true, coefficient := (-329470203172410340771556259 / 250000000000000000000000000000 : Rat) }, { recordIndex := 614, useUpper := true, coefficient := (-2286119774125271968481307231 / 250000000000000000000000000000 : Rat) }, { recordIndex := 615, useUpper := true, coefficient := (-5231175168108680599015201977 / 500000000000000000000000000000 : Rat) }, { recordIndex := 616, useUpper := true, coefficient := (-187912757178079275464022183561 / 500000000000000000000000000000 : Rat) }, { recordIndex := 617, useUpper := true, coefficient := (-249715984433928141295638611163 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 618, useUpper := false, coefficient := (209135311860531 / 2000000000000000 : Rat) }, { recordIndex := 619, useUpper := true, coefficient := (-4850963467584728576601739017 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 620, useUpper := true, coefficient := (-353817878701588746485857383 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 621, useUpper := true, coefficient := (-4752284359939098228851255553 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 622, useUpper := true, coefficient := (-353817878701588746485857383 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 623, useUpper := true, coefficient := (-2360158183660205357651331249 / 62500000000000000000000000000 : Rat) }, { recordIndex := 624, useUpper := true, coefficient := (-66451307113000625531092842633 / 500000000000000000000000000000 : Rat) }, { recordIndex := 625, useUpper := true, coefficient := (-32960907024801372319694802699 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 626, useUpper := false, coefficient := (112343 / 400000000000000 : Rat) }, { recordIndex := 627, useUpper := true, coefficient := (-381413459753442039 / 6250000000000000000000000000 : Rat) }, { recordIndex := 628, useUpper := true, coefficient := (-2372979852371917173 / 40000000000000000000000000000 : Rat) }, { recordIndex := 629, useUpper := true, coefficient := (-23743686590312663359 / 400000000000000000000000000000 : Rat) }, { recordIndex := 630, useUpper := true, coefficient := (-21030668535778492129 / 400000000000000000000000000000 : Rat) }, { recordIndex := 631, useUpper := true, coefficient := (-2372979852371917173 / 40000000000000000000000000000 : Rat) }, { recordIndex := 632, useUpper := true, coefficient := (-9630829602906590771 / 80000000000000000000000000000 : Rat) }, { recordIndex := 633, useUpper := true, coefficient := (-8091810692349574883 / 80000000000000000000000000000 : Rat) }, { recordIndex := 634, useUpper := true, coefficient := (-9714192462984691143 / 200000000000000000000000000000 : Rat) }, { recordIndex := 635, useUpper := false, coefficient := (395432343788877 / 1000000000000000 : Rat) }, { recordIndex := 636, useUpper := true, coefficient := (-329470203172410340771556259 / 250000000000000000000000000000 : Rat) }, { recordIndex := 637, useUpper := true, coefficient := (-2286119774125271968481307231 / 250000000000000000000000000000 : Rat) }, { recordIndex := 638, useUpper := true, coefficient := (-4572234761763859917472089459 / 500000000000000000000000000000 : Rat) }, { recordIndex := 639, useUpper := true, coefficient := (-126109529922230409632405755959 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 640, useUpper := true, coefficient := (-2286119774125271968481307231 / 250000000000000000000000000000 : Rat) }, { recordIndex := 641, useUpper := true, coefficient := (-5231175168108680599015201977 / 500000000000000000000000000000 : Rat) }, { recordIndex := 642, useUpper := true, coefficient := (-187912757178079275464022183561 / 500000000000000000000000000000 : Rat) }, { recordIndex := 643, useUpper := true, coefficient := (-249715984433928141295638611163 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 644, useUpper := false, coefficient := (209135311860531 / 2000000000000000 : Rat) }, { recordIndex := 645, useUpper := true, coefficient := (-4752284359939098228851255553 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 646, useUpper := true, coefficient := (-353817878701588746485857383 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 647, useUpper := true, coefficient := (-4850963467584728576601739017 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 648, useUpper := true, coefficient := (-353817878701588746485857383 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 649, useUpper := true, coefficient := (-2360158183660205357651331249 / 62500000000000000000000000000 : Rat) }, { recordIndex := 650, useUpper := true, coefficient := (-66451307113000625531092842633 / 500000000000000000000000000000 : Rat) }, { recordIndex := 651, useUpper := true, coefficient := (-32960907024801372319694802699 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 652, useUpper := false, coefficient := (112343 / 400000000000000 : Rat) }, { recordIndex := 653, useUpper := true, coefficient := (-23743686590312663359 / 400000000000000000000000000000 : Rat) }, { recordIndex := 654, useUpper := true, coefficient := (-21030668535778492129 / 400000000000000000000000000000 : Rat) }, { recordIndex := 655, useUpper := true, coefficient := (-2372979852371917173 / 40000000000000000000000000000 : Rat) }, { recordIndex := 656, useUpper := true, coefficient := (-381413459753442039 / 6250000000000000000000000000 : Rat) }, { recordIndex := 657, useUpper := true, coefficient := (-2372979852371917173 / 40000000000000000000000000000 : Rat) }, { recordIndex := 658, useUpper := true, coefficient := (-9630829602906590771 / 80000000000000000000000000000 : Rat) }, { recordIndex := 659, useUpper := true, coefficient := (-8091810692349574883 / 80000000000000000000000000000 : Rat) }, { recordIndex := 660, useUpper := true, coefficient := (-9714192462984691143 / 200000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (167710777527 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 670, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 671, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 672, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (484767435211 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 673, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 674, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 675, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 676, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 677, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 678, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (281768877129 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 679, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 680, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 681, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 682, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 683, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 684, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 685, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 686, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 687, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (796994196939 / 1000000000000 : Rat)
    constant := (-1402332859571396020587453419888139120101063993 / 1000000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 738, useUpper := false, coefficient := (657773 / 2000000000000000 : Rat) }, { recordIndex := 739, useUpper := false, coefficient := (657773 / 2000000000000000 : Rat) }, { recordIndex := 740, useUpper := false, coefficient := (657773 / 1000000000000000 : Rat) }, { recordIndex := 741, useUpper := false, coefficient := (638984297351471 / 2000000000000000 : Rat) }, { recordIndex := 742, useUpper := false, coefficient := (638984297351471 / 2000000000000000 : Rat) }, { recordIndex := 743, useUpper := false, coefficient := (638984297351471 / 1000000000000000 : Rat) }, { recordIndex := 744, useUpper := false, coefficient := (90253925497689 / 500000000000000 : Rat) }, { recordIndex := 745, useUpper := false, coefficient := (90253925497689 / 500000000000000 : Rat) }, { recordIndex := 746, useUpper := false, coefficient := (90253925497689 / 250000000000000 : Rat) }]
  },
  {
    retainedFloor := (796994196939 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 688, useUpper := false, coefficient := (657773 / 2000000000000000 : Rat) }, { recordIndex := 689, useUpper := true, coefficient := (-24274917201858659791 / 400000000000000000000000000000 : Rat) }, { recordIndex := 690, useUpper := true, coefficient := (-144736486079358679033 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 691, useUpper := true, coefficient := (-178711323246113942273 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 692, useUpper := true, coefficient := (-178711323246113942273 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 693, useUpper := true, coefficient := (-266066209097479012001 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 694, useUpper := true, coefficient := (-281254449233455412419 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 695, useUpper := true, coefficient := (-72345811544092856523 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 696, useUpper := false, coefficient := (638984297351471 / 2000000000000000 : Rat) }, { recordIndex := 697, useUpper := true, coefficient := (-428429854978162164792376819 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 698, useUpper := true, coefficient := (-36379921265608075460651493577 / 400000000000000000000000000000 : Rat) }, { recordIndex := 699, useUpper := true, coefficient := (-52181448080283879784592483867 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 700, useUpper := true, coefficient := (-428429854978162164792376819 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 701, useUpper := true, coefficient := (-231061602541289224013811417571 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 702, useUpper := true, coefficient := (-762807081830123347858199927353 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 703, useUpper := true, coefficient := (-24580998106624423355276974843 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 704, useUpper := false, coefficient := (90253925497689 / 500000000000000 : Rat) }, { recordIndex := 705, useUpper := true, coefficient := (-61566750580439732292568527 / 500000000000000000000000000000 : Rat) }, { recordIndex := 706, useUpper := true, coefficient := (-7341079583739235919304276417 / 500000000000000000000000000000 : Rat) }, { recordIndex := 707, useUpper := true, coefficient := (-6421853837226829433390401473 / 125000000000000000000000000000 : Rat) }, { recordIndex := 708, useUpper := true, coefficient := (-366645782297331224561165067 / 25000000000000000000000000000 : Rat) }, { recordIndex := 709, useUpper := true, coefficient := (-6421853837226829433390401473 / 125000000000000000000000000000 : Rat) }, { recordIndex := 710, useUpper := true, coefficient := (-61566750580439732292568527 / 500000000000000000000000000000 : Rat) }, { recordIndex := 711, useUpper := true, coefficient := (-14673995229685860410527577757 / 500000000000000000000000000000 : Rat) }, { recordIndex := 712, useUpper := true, coefficient := (-3114434260532211382726140489 / 15625000000000000000000000000 : Rat) }, { recordIndex := 713, useUpper := false, coefficient := (657773 / 2000000000000000 : Rat) }, { recordIndex := 714, useUpper := true, coefficient := (-178711323246113942273 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 715, useUpper := true, coefficient := (-24274917201858659791 / 400000000000000000000000000000 : Rat) }, { recordIndex := 716, useUpper := true, coefficient := (-144736486079358679033 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 717, useUpper := true, coefficient := (-178711323246113942273 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 718, useUpper := true, coefficient := (-266066209097479012001 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 719, useUpper := true, coefficient := (-281254449233455412419 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 720, useUpper := true, coefficient := (-72345811544092856523 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 721, useUpper := false, coefficient := (638984297351471 / 2000000000000000 : Rat) }, { recordIndex := 722, useUpper := true, coefficient := (-36379921265608075460651493577 / 400000000000000000000000000000 : Rat) }, { recordIndex := 723, useUpper := true, coefficient := (-52181448080283879784592483867 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 724, useUpper := true, coefficient := (-428429854978162164792376819 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 725, useUpper := true, coefficient := (-428429854978162164792376819 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 726, useUpper := true, coefficient := (-231061602541289224013811417571 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 727, useUpper := true, coefficient := (-762807081830123347858199927353 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 728, useUpper := true, coefficient := (-24580998106624423355276974843 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 729, useUpper := false, coefficient := (90253925497689 / 500000000000000 : Rat) }, { recordIndex := 730, useUpper := true, coefficient := (-61566750580439732292568527 / 500000000000000000000000000000 : Rat) }, { recordIndex := 731, useUpper := true, coefficient := (-366645782297331224561165067 / 25000000000000000000000000000 : Rat) }, { recordIndex := 732, useUpper := true, coefficient := (-6421853837226829433390401473 / 125000000000000000000000000000 : Rat) }, { recordIndex := 733, useUpper := true, coefficient := (-7341079583739235919304276417 / 500000000000000000000000000000 : Rat) }, { recordIndex := 734, useUpper := true, coefficient := (-6421853837226829433390401473 / 125000000000000000000000000000 : Rat) }, { recordIndex := 735, useUpper := true, coefficient := (-61566750580439732292568527 / 500000000000000000000000000000 : Rat) }, { recordIndex := 736, useUpper := true, coefficient := (-14673995229685860410527577757 / 500000000000000000000000000000 : Rat) }, { recordIndex := 737, useUpper := true, coefficient := (-3114434260532211382726140489 / 15625000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (434305057859 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 747, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 748, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 749, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (462457871897 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 750, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 751, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 752, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 753, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 754, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 755, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (63092603951 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 756, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 757, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 758, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 759, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 760, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 761, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 762, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 763, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 764, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (790305734093 / 1000000000000 : Rat)
    constant := (-1409685082343853411317491818114967027289615587 / 1000000000000001000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 803, useUpper := false, coefficient := (276650003987615 / 1000000000000001 : Rat) }, { recordIndex := 804, useUpper := false, coefficient := (276650003987615 / 1000000000000001 : Rat) }, { recordIndex := 805, useUpper := false, coefficient := (553300007975230 / 1000000000000001 : Rat) }, { recordIndex := 806, useUpper := false, coefficient := (223349996012207 / 1000000000000001 : Rat) }, { recordIndex := 807, useUpper := false, coefficient := (223349996012207 / 1000000000000001 : Rat) }, { recordIndex := 808, useUpper := false, coefficient := (446699992024414 / 1000000000000001 : Rat) }, { recordIndex := 809, useUpper := false, coefficient := (51 / 285714285714286 : Rat) }, { recordIndex := 810, useUpper := false, coefficient := (51 / 285714285714286 : Rat) }, { recordIndex := 811, useUpper := false, coefficient := (51 / 142857142857143 : Rat) }]
  },
  {
    retainedFloor := (790305734093 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 765, useUpper := false, coefficient := (276650003987615 / 1000000000000001 : Rat) }, { recordIndex := 766, useUpper := true, coefficient := (-4846511822987407413542020679 / 50000000000000050000000000000 : Rat) }, { recordIndex := 767, useUpper := true, coefficient := (-114913955617344324075986541 / 28571428571428600000000000000 : Rat) }, { recordIndex := 768, useUpper := true, coefficient := (-4956873009836508157406190383 / 18181818181818200000000000000 : Rat) }, { recordIndex := 769, useUpper := true, coefficient := (-816908034217576598768907211 / 4545454545454550000000000000 : Rat) }, { recordIndex := 770, useUpper := false, coefficient := (223349996012207 / 1000000000000001 : Rat) }, { recordIndex := 771, useUpper := true, coefficient := (-39235921713123535456760790263 / 500000000000000500000000000000 : Rat) }, { recordIndex := 772, useUpper := true, coefficient := (-70881945121365537989101587841 / 500000000000000500000000000000 : Rat) }, { recordIndex := 773, useUpper := true, coefficient := (-27805913778829045609600391 / 8928571428571437500000000000 : Rat) }, { recordIndex := 774, useUpper := true, coefficient := (-39235921713123535456760790263 / 500000000000000500000000000000 : Rat) }, { recordIndex := 775, useUpper := true, coefficient := (-70881945121365537989101587841 / 500000000000000500000000000000 : Rat) }, { recordIndex := 776, useUpper := true, coefficient := (-27805913778829045609600391 / 8928571428571437500000000000 : Rat) }, { recordIndex := 777, useUpper := false, coefficient := (51 / 285714285714286 : Rat) }, { recordIndex := 778, useUpper := true, coefficient := (-215404333732563 / 3571428571428575000000000000 : Rat) }, { recordIndex := 779, useUpper := true, coefficient := (-2124720159538749 / 35714285714285750000000000000 : Rat) }, { recordIndex := 780, useUpper := true, coefficient := (-190566954830511 / 3246753246753250000000000000 : Rat) }, { recordIndex := 781, useUpper := true, coefficient := (-190566954830511 / 3246753246753250000000000000 : Rat) }, { recordIndex := 782, useUpper := true, coefficient := (-215404333732563 / 3571428571428575000000000000 : Rat) }, { recordIndex := 783, useUpper := true, coefficient := (-2124720159538749 / 35714285714285750000000000000 : Rat) }, { recordIndex := 784, useUpper := false, coefficient := (276650003987615 / 1000000000000001 : Rat) }, { recordIndex := 785, useUpper := true, coefficient := (-4846511822987407413542020679 / 50000000000000050000000000000 : Rat) }, { recordIndex := 786, useUpper := true, coefficient := (-114913955617344324075986541 / 28571428571428600000000000000 : Rat) }, { recordIndex := 787, useUpper := true, coefficient := (-4956873009836508157406190383 / 18181818181818200000000000000 : Rat) }, { recordIndex := 788, useUpper := true, coefficient := (-816908034217576598768907211 / 4545454545454550000000000000 : Rat) }, { recordIndex := 789, useUpper := false, coefficient := (223349996012207 / 1000000000000001 : Rat) }, { recordIndex := 790, useUpper := true, coefficient := (-39235921713123535456760790263 / 500000000000000500000000000000 : Rat) }, { recordIndex := 791, useUpper := true, coefficient := (-70881945121365537989101587841 / 500000000000000500000000000000 : Rat) }, { recordIndex := 792, useUpper := true, coefficient := (-27805913778829045609600391 / 8928571428571437500000000000 : Rat) }, { recordIndex := 793, useUpper := true, coefficient := (-39235921713123535456760790263 / 500000000000000500000000000000 : Rat) }, { recordIndex := 794, useUpper := true, coefficient := (-70881945121365537989101587841 / 500000000000000500000000000000 : Rat) }, { recordIndex := 795, useUpper := true, coefficient := (-27805913778829045609600391 / 8928571428571437500000000000 : Rat) }, { recordIndex := 796, useUpper := false, coefficient := (51 / 285714285714286 : Rat) }, { recordIndex := 797, useUpper := true, coefficient := (-215404333732563 / 3571428571428575000000000000 : Rat) }, { recordIndex := 798, useUpper := true, coefficient := (-190566954830511 / 3246753246753250000000000000 : Rat) }, { recordIndex := 799, useUpper := true, coefficient := (-2124720159538749 / 35714285714285750000000000000 : Rat) }, { recordIndex := 800, useUpper := true, coefficient := (-190566954830511 / 3246753246753250000000000000 : Rat) }, { recordIndex := 801, useUpper := true, coefficient := (-215404333732563 / 3571428571428575000000000000 : Rat) }, { recordIndex := 802, useUpper := true, coefficient := (-2124720159538749 / 35714285714285750000000000000 : Rat) }]
  },
  {
    retainedFloor := (704380756951 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 812, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 813, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 814, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (714163703507 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 815, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 816, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 817, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (258884040259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 818, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 819, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 820, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (466854906987 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 821, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 822, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 823, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 824, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 825, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 826, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (15170925051 / 50000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 827, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 828, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 829, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 830, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 831, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 832, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 833, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 834, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 835, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (2674999097 / 3906250000 : Rat)
    constant := (-235041025249741255543861561136887819862834603 / 200000000000000200000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 884, useUpper := false, coefficient := (556530395382917 / 2000000000000002 : Rat) }, { recordIndex := 885, useUpper := false, coefficient := (556530395382917 / 2000000000000002 : Rat) }, { recordIndex := 886, useUpper := false, coefficient := (556530395382917 / 1000000000000001 : Rat) }, { recordIndex := 887, useUpper := false, coefficient := (221734795599600 / 1000000000000001 : Rat) }, { recordIndex := 888, useUpper := false, coefficient := (221734795599600 / 1000000000000001 : Rat) }, { recordIndex := 889, useUpper := false, coefficient := (443469591199200 / 1000000000000001 : Rat) }, { recordIndex := 890, useUpper := false, coefficient := (6708942 / 1000000000000001 : Rat) }, { recordIndex := 891, useUpper := false, coefficient := (6708942 / 1000000000000001 : Rat) }, { recordIndex := 892, useUpper := false, coefficient := (13417884 / 1000000000000001 : Rat) }]
  },
  {
    retainedFloor := (2674999097 / 3906250000 : Rat)
    constant := 0
    terms := [{ recordIndex := 836, useUpper := false, coefficient := (556530395382917 / 2000000000000002 : Rat) }, { recordIndex := 837, useUpper := true, coefficient := (-309193875207099453798451 / 35714285714285750000000000000 : Rat) }, { recordIndex := 838, useUpper := true, coefficient := (-14822447819687360437768383899 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 839, useUpper := true, coefficient := (-33738228768894793198752904709 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 840, useUpper := true, coefficient := (-474214175168428455595313093427 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 841, useUpper := true, coefficient := (-14822447819687360437768383899 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 842, useUpper := true, coefficient := (-309193875207099453798451 / 35714285714285750000000000000 : Rat) }, { recordIndex := 843, useUpper := true, coefficient := (-33738228768894793198752904709 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 844, useUpper := true, coefficient := (-474214175168428455595313093427 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 845, useUpper := false, coefficient := (221734795599600 / 1000000000000001 : Rat) }, { recordIndex := 846, useUpper := true, coefficient := (-2687565053606325931653 / 446428571428571875000000 : Rat) }, { recordIndex := 847, useUpper := true, coefficient := (-29810575321288320011745531 / 156250000000000156250000000 : Rat) }, { recordIndex := 848, useUpper := true, coefficient := (-62300462714632025015391537 / 2500000000000002500000000000 : Rat) }, { recordIndex := 849, useUpper := true, coefficient := (-1541531232675416311197 / 227272727272727500000000000 : Rat) }, { recordIndex := 850, useUpper := true, coefficient := (-1541531232675416311197 / 227272727272727500000000000 : Rat) }, { recordIndex := 851, useUpper := true, coefficient := (-2687565053606325931653 / 446428571428571875000000 : Rat) }, { recordIndex := 852, useUpper := true, coefficient := (-29810575321288320011745531 / 156250000000000156250000000 : Rat) }, { recordIndex := 853, useUpper := true, coefficient := (-62300462714632025015391537 / 2500000000000002500000000000 : Rat) }, { recordIndex := 854, useUpper := false, coefficient := (6708942 / 1000000000000001 : Rat) }, { recordIndex := 855, useUpper := true, coefficient := (-37650509919356051691 / 19230769230769250000000000000 : Rat) }, { recordIndex := 856, useUpper := true, coefficient := (-37129622808187522881 / 25000000000000025000000000000 : Rat) }, { recordIndex := 857, useUpper := true, coefficient := (-37650509919356051691 / 19230769230769250000000000000 : Rat) }, { recordIndex := 858, useUpper := true, coefficient := (-1187778871048371328017 / 250000000000000250000000000000 : Rat) }, { recordIndex := 859, useUpper := true, coefficient := (-816482642966496099207 / 250000000000000250000000000000 : Rat) }, { recordIndex := 860, useUpper := false, coefficient := (556530395382917 / 2000000000000002 : Rat) }, { recordIndex := 861, useUpper := true, coefficient := (-309193875207099453798451 / 35714285714285750000000000000 : Rat) }, { recordIndex := 862, useUpper := true, coefficient := (-33738228768894793198752904709 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 863, useUpper := true, coefficient := (-474214175168428455595313093427 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 864, useUpper := true, coefficient := (-14822447819687360437768383899 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 865, useUpper := true, coefficient := (-14822447819687360437768383899 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 866, useUpper := true, coefficient := (-309193875207099453798451 / 35714285714285750000000000000 : Rat) }, { recordIndex := 867, useUpper := true, coefficient := (-33738228768894793198752904709 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 868, useUpper := true, coefficient := (-474214175168428455595313093427 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 869, useUpper := false, coefficient := (221734795599600 / 1000000000000001 : Rat) }, { recordIndex := 870, useUpper := true, coefficient := (-1541531232675416311197 / 227272727272727500000000000 : Rat) }, { recordIndex := 871, useUpper := true, coefficient := (-2687565053606325931653 / 446428571428571875000000 : Rat) }, { recordIndex := 872, useUpper := true, coefficient := (-29810575321288320011745531 / 156250000000000156250000000 : Rat) }, { recordIndex := 873, useUpper := true, coefficient := (-62300462714632025015391537 / 2500000000000002500000000000 : Rat) }, { recordIndex := 874, useUpper := true, coefficient := (-1541531232675416311197 / 227272727272727500000000000 : Rat) }, { recordIndex := 875, useUpper := true, coefficient := (-2687565053606325931653 / 446428571428571875000000 : Rat) }, { recordIndex := 876, useUpper := true, coefficient := (-29810575321288320011745531 / 156250000000000156250000000 : Rat) }, { recordIndex := 877, useUpper := true, coefficient := (-62300462714632025015391537 / 2500000000000002500000000000 : Rat) }, { recordIndex := 878, useUpper := false, coefficient := (6708942 / 1000000000000001 : Rat) }, { recordIndex := 879, useUpper := true, coefficient := (-37129622808187522881 / 25000000000000025000000000000 : Rat) }, { recordIndex := 880, useUpper := true, coefficient := (-37650509919356051691 / 19230769230769250000000000000 : Rat) }, { recordIndex := 881, useUpper := true, coefficient := (-37650509919356051691 / 19230769230769250000000000000 : Rat) }, { recordIndex := 882, useUpper := true, coefficient := (-1187778871048371328017 / 250000000000000250000000000000 : Rat) }, { recordIndex := 883, useUpper := true, coefficient := (-816482642966496099207 / 250000000000000250000000000000 : Rat) }]
  },
  {
    retainedFloor := (162452623933 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 893, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 894, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 895, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (486492662951 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 896, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 897, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 898, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 899, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 900, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 901, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (343654213397 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 902, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 903, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 904, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 905, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 906, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 907, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 908, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 909, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 910, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (426276034661 / 500000000000 : Rat)
    constant := (-96275461974305842319536441144725097404510663 / 62500000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 963, useUpper := false, coefficient := (2778081 / 400000000000000 : Rat) }, { recordIndex := 964, useUpper := false, coefficient := (2778081 / 400000000000000 : Rat) }, { recordIndex := 965, useUpper := false, coefficient := (2778081 / 200000000000000 : Rat) }, { recordIndex := 966, useUpper := false, coefficient := (99204268572423 / 250000000000000 : Rat) }, { recordIndex := 967, useUpper := false, coefficient := (99204268572423 / 250000000000000 : Rat) }, { recordIndex := 968, useUpper := false, coefficient := (99204268572423 / 125000000000000 : Rat) }, { recordIndex := 969, useUpper := false, coefficient := (206365837530211 / 2000000000000000 : Rat) }, { recordIndex := 970, useUpper := false, coefficient := (206365837530211 / 2000000000000000 : Rat) }, { recordIndex := 971, useUpper := false, coefficient := (206365837530211 / 1000000000000000 : Rat) }]
  },
  {
    retainedFloor := (426276034661 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 911, useUpper := false, coefficient := (2778081 / 400000000000000 : Rat) }, { recordIndex := 912, useUpper := true, coefficient := (-74320283992073191773 / 50000000000000000000000000000 : Rat) }, { recordIndex := 913, useUpper := true, coefficient := (-292008525139874145597 / 200000000000000000000000000000 : Rat) }, { recordIndex := 914, useUpper := true, coefficient := (-57923309990560210623 / 40000000000000000000000000000 : Rat) }, { recordIndex := 915, useUpper := true, coefficient := (-263216743663612011519 / 200000000000000000000000000000 : Rat) }, { recordIndex := 916, useUpper := true, coefficient := (-292008525139874145597 / 200000000000000000000000000000 : Rat) }, { recordIndex := 917, useUpper := true, coefficient := (-586897685921093820207 / 200000000000000000000000000000 : Rat) }, { recordIndex := 918, useUpper := true, coefficient := (-127533572234758008549 / 50000000000000000000000000000 : Rat) }, { recordIndex := 919, useUpper := true, coefficient := (-246917545275420022677 / 200000000000000000000000000000 : Rat) }, { recordIndex := 920, useUpper := false, coefficient := (99204268572423 / 250000000000000 : Rat) }, { recordIndex := 921, useUpper := true, coefficient := (-46170623273838608835524997 / 5000000000000000000000000000 : Rat) }, { recordIndex := 922, useUpper := true, coefficient := (-31684815238921677645173245647 / 250000000000000000000000000000 : Rat) }, { recordIndex := 923, useUpper := true, coefficient := (-2272685534943021229147348113 / 250000000000000000000000000000 : Rat) }, { recordIndex := 924, useUpper := true, coefficient := (-82141813623938516071652889 / 62500000000000000000000000000 : Rat) }, { recordIndex := 925, useUpper := true, coefficient := (-2272685534943021229147348113 / 250000000000000000000000000000 : Rat) }, { recordIndex := 926, useUpper := true, coefficient := (-1318549209093842253031430703 / 125000000000000000000000000000 : Rat) }, { recordIndex := 927, useUpper := true, coefficient := (-94294484619292294264789790481 / 250000000000000000000000000000 : Rat) }, { recordIndex := 928, useUpper := true, coefficient := (-31304834690185308309808272417 / 125000000000000000000000000000 : Rat) }, { recordIndex := 929, useUpper := false, coefficient := (206365837530211 / 2000000000000000 : Rat) }, { recordIndex := 930, useUpper := true, coefficient := (-2373373224749048501503358467 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 931, useUpper := true, coefficient := (-707809189499853924251880051 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 932, useUpper := true, coefficient := (-4758695887022980698090110689 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 933, useUpper := true, coefficient := (-707809189499853924251880051 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 934, useUpper := true, coefficient := (-74360845114655805442393716367 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 935, useUpper := true, coefficient := (-65648591613027670316677201791 / 500000000000000000000000000000 : Rat) }, { recordIndex := 936, useUpper := true, coefficient := (-8106925347266840967662111093 / 250000000000000000000000000000 : Rat) }, { recordIndex := 937, useUpper := false, coefficient := (2778081 / 400000000000000 : Rat) }, { recordIndex := 938, useUpper := true, coefficient := (-57923309990560210623 / 40000000000000000000000000000 : Rat) }, { recordIndex := 939, useUpper := true, coefficient := (-263216743663612011519 / 200000000000000000000000000000 : Rat) }, { recordIndex := 940, useUpper := true, coefficient := (-292008525139874145597 / 200000000000000000000000000000 : Rat) }, { recordIndex := 941, useUpper := true, coefficient := (-74320283992073191773 / 50000000000000000000000000000 : Rat) }, { recordIndex := 942, useUpper := true, coefficient := (-292008525139874145597 / 200000000000000000000000000000 : Rat) }, { recordIndex := 943, useUpper := true, coefficient := (-586897685921093820207 / 200000000000000000000000000000 : Rat) }, { recordIndex := 944, useUpper := true, coefficient := (-127533572234758008549 / 50000000000000000000000000000 : Rat) }, { recordIndex := 945, useUpper := true, coefficient := (-246917545275420022677 / 200000000000000000000000000000 : Rat) }, { recordIndex := 946, useUpper := false, coefficient := (99204268572423 / 250000000000000 : Rat) }, { recordIndex := 947, useUpper := true, coefficient := (-82141813623938516071652889 / 62500000000000000000000000000 : Rat) }, { recordIndex := 948, useUpper := true, coefficient := (-2272685534943021229147348113 / 250000000000000000000000000000 : Rat) }, { recordIndex := 949, useUpper := true, coefficient := (-46170623273838608835524997 / 5000000000000000000000000000 : Rat) }, { recordIndex := 950, useUpper := true, coefficient := (-31684815238921677645173245647 / 250000000000000000000000000000 : Rat) }, { recordIndex := 951, useUpper := true, coefficient := (-2272685534943021229147348113 / 250000000000000000000000000000 : Rat) }, { recordIndex := 952, useUpper := true, coefficient := (-1318549209093842253031430703 / 125000000000000000000000000000 : Rat) }, { recordIndex := 953, useUpper := true, coefficient := (-94294484619292294264789790481 / 250000000000000000000000000000 : Rat) }, { recordIndex := 954, useUpper := true, coefficient := (-31304834690185308309808272417 / 125000000000000000000000000000 : Rat) }, { recordIndex := 955, useUpper := false, coefficient := (206365837530211 / 2000000000000000 : Rat) }, { recordIndex := 956, useUpper := true, coefficient := (-4758695887022980698090110689 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 957, useUpper := true, coefficient := (-707809189499853924251880051 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 958, useUpper := true, coefficient := (-2373373224749048501503358467 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 959, useUpper := true, coefficient := (-707809189499853924251880051 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 960, useUpper := true, coefficient := (-74360845114655805442393716367 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 961, useUpper := true, coefficient := (-65648591613027670316677201791 / 500000000000000000000000000000 : Rat) }, { recordIndex := 962, useUpper := true, coefficient := (-8106925347266840967662111093 / 250000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (171660393567 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 972, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 973, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 974, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (12162638611 / 25000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 975, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 976, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 977, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 978, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 979, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 980, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (324932428981 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 981, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 982, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 983, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 984, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 985, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 986, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 987, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 988, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 989, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (853161978061 / 1000000000000 : Rat)
    constant := (-770872871665418794270029992016915829717432853 / 500000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1042, useUpper := false, coefficient := (25822792276761 / 250000000000000 : Rat) }, { recordIndex := 1043, useUpper := false, coefficient := (25822792276761 / 250000000000000 : Rat) }, { recordIndex := 1044, useUpper := false, coefficient := (25822792276761 / 125000000000000 : Rat) }, { recordIndex := 1045, useUpper := false, coefficient := (79341764621967 / 200000000000000 : Rat) }, { recordIndex := 1046, useUpper := false, coefficient := (79341764621967 / 200000000000000 : Rat) }, { recordIndex := 1047, useUpper := false, coefficient := (79341764621967 / 100000000000000 : Rat) }, { recordIndex := 1048, useUpper := false, coefficient := (7783121 / 1000000000000000 : Rat) }, { recordIndex := 1049, useUpper := false, coefficient := (7783121 / 1000000000000000 : Rat) }, { recordIndex := 1050, useUpper := false, coefficient := (7783121 / 500000000000000 : Rat) }]
  },
  {
    retainedFloor := (853161978061 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 990, useUpper := false, coefficient := (25822792276761 / 250000000000000 : Rat) }, { recordIndex := 991, useUpper := true, coefficient := (-18682723721929256628680691 / 7812500000000000000000000000 : Rat) }, { recordIndex := 992, useUpper := true, coefficient := (-89006271909764645039405229 / 250000000000000000000000000000 : Rat) }, { recordIndex := 993, useUpper := true, coefficient := (-599159228562278764471802091 / 250000000000000000000000000000 : Rat) }, { recordIndex := 994, useUpper := true, coefficient := (-89006271909764645039405229 / 250000000000000000000000000000 : Rat) }, { recordIndex := 995, useUpper := true, coefficient := (-1164973088369627814341190801 / 31250000000000000000000000000 : Rat) }, { recordIndex := 996, useUpper := true, coefficient := (-16414001297894212840231068363 / 125000000000000000000000000000 : Rat) }, { recordIndex := 997, useUpper := true, coefficient := (-1624555663858601507627988441 / 50000000000000000000000000000 : Rat) }, { recordIndex := 998, useUpper := false, coefficient := (79341764621967 / 200000000000000 : Rat) }, { recordIndex := 999, useUpper := true, coefficient := (-133951193727339422246258007 / 100000000000000000000000000000 : Rat) }, { recordIndex := 1000, useUpper := true, coefficient := (-922139071622171067868319907 / 100000000000000000000000000000 : Rat) }, { recordIndex := 1001, useUpper := true, coefficient := (-1853664449789448604148322717 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1002, useUpper := true, coefficient := (-25295031597175501573627581627 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1003, useUpper := true, coefficient := (-922139071622171067868319907 / 100000000000000000000000000000 : Rat) }, { recordIndex := 1004, useUpper := true, coefficient := (-2121566837244127448640838731 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1005, useUpper := true, coefficient := (-15075183928295706083124504291 / 40000000000000000000000000000 : Rat) }, { recordIndex := 1006, useUpper := true, coefficient := (-12520222011075757210498734957 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1007, useUpper := false, coefficient := (7783121 / 1000000000000000 : Rat) }, { recordIndex := 1008, useUpper := true, coefficient := (-1465310450090712373549 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1009, useUpper := true, coefficient := (-870641606439767818591 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1010, useUpper := true, coefficient := (-182901118965566881501 / 125000000000000000000000000000 : Rat) }, { recordIndex := 1011, useUpper := true, coefficient := (-1300445304689407971567 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1012, useUpper := true, coefficient := (-182901118965566881501 / 125000000000000000000000000000 : Rat) }, { recordIndex := 1013, useUpper := true, coefficient := (-691438938695030086279 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1014, useUpper := true, coefficient := (-888539073373836150719 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1015, useUpper := true, coefficient := (-906436540307904482847 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1016, useUpper := false, coefficient := (25822792276761 / 250000000000000 : Rat) }, { recordIndex := 1017, useUpper := true, coefficient := (-599159228562278764471802091 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1018, useUpper := true, coefficient := (-89006271909764645039405229 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1019, useUpper := true, coefficient := (-18682723721929256628680691 / 7812500000000000000000000000 : Rat) }, { recordIndex := 1020, useUpper := true, coefficient := (-89006271909764645039405229 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1021, useUpper := true, coefficient := (-1164973088369627814341190801 / 31250000000000000000000000000 : Rat) }, { recordIndex := 1022, useUpper := true, coefficient := (-16414001297894212840231068363 / 125000000000000000000000000000 : Rat) }, { recordIndex := 1023, useUpper := true, coefficient := (-1624555663858601507627988441 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1024, useUpper := false, coefficient := (79341764621967 / 200000000000000 : Rat) }, { recordIndex := 1025, useUpper := true, coefficient := (-1853664449789448604148322717 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1026, useUpper := true, coefficient := (-25295031597175501573627581627 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1027, useUpper := true, coefficient := (-922139071622171067868319907 / 100000000000000000000000000000 : Rat) }, { recordIndex := 1028, useUpper := true, coefficient := (-133951193727339422246258007 / 100000000000000000000000000000 : Rat) }, { recordIndex := 1029, useUpper := true, coefficient := (-922139071622171067868319907 / 100000000000000000000000000000 : Rat) }, { recordIndex := 1030, useUpper := true, coefficient := (-2121566837244127448640838731 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1031, useUpper := true, coefficient := (-15075183928295706083124504291 / 40000000000000000000000000000 : Rat) }, { recordIndex := 1032, useUpper := true, coefficient := (-12520222011075757210498734957 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1033, useUpper := false, coefficient := (7783121 / 1000000000000000 : Rat) }, { recordIndex := 1034, useUpper := true, coefficient := (-1300445304689407971567 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1035, useUpper := true, coefficient := (-182901118965566881501 / 125000000000000000000000000000 : Rat) }, { recordIndex := 1036, useUpper := true, coefficient := (-1465310450090712373549 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1037, useUpper := true, coefficient := (-870641606439767818591 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1038, useUpper := true, coefficient := (-182901118965566881501 / 125000000000000000000000000000 : Rat) }, { recordIndex := 1039, useUpper := true, coefficient := (-691438938695030086279 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1040, useUpper := true, coefficient := (-888539073373836150719 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1041, useUpper := true, coefficient := (-906436540307904482847 / 500000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (303490810493 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1051, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1052, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1053, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (466598344303 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1054, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1055, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1056, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1057, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1058, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1059, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (130406972043 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1060, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1061, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1062, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1063, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1064, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1065, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1066, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1067, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1068, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (697980110907 / 1000000000000 : Rat)
    constant := (-301498844328536555260172581265004216243192819 / 250000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1117, useUpper := false, coefficient := 0 }, { recordIndex := 1118, useUpper := false, coefficient := 0 }, { recordIndex := 1119, useUpper := false, coefficient := 0 }, { recordIndex := 1120, useUpper := false, coefficient := (217031423202167 / 1000000000000000 : Rat) }, { recordIndex := 1121, useUpper := false, coefficient := (217031423202167 / 1000000000000000 : Rat) }, { recordIndex := 1122, useUpper := false, coefficient := (217031423202167 / 500000000000000 : Rat) }, { recordIndex := 1123, useUpper := false, coefficient := (282968576797833 / 1000000000000000 : Rat) }, { recordIndex := 1124, useUpper := false, coefficient := (282968576797833 / 1000000000000000 : Rat) }, { recordIndex := 1125, useUpper := false, coefficient := (282968576797833 / 500000000000000 : Rat) }]
  },
  {
    retainedFloor := (697980110907 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1069, useUpper := false, coefficient := 0 }, { recordIndex := 1070, useUpper := true, coefficient := 0 }, { recordIndex := 1071, useUpper := true, coefficient := 0 }, { recordIndex := 1072, useUpper := true, coefficient := 0 }, { recordIndex := 1073, useUpper := true, coefficient := 0 }, { recordIndex := 1074, useUpper := true, coefficient := 0 }, { recordIndex := 1075, useUpper := false, coefficient := (217031423202167 / 1000000000000000 : Rat) }, { recordIndex := 1076, useUpper := true, coefficient := (-1905141752977511462991479 / 12500000000000000000000000000 : Rat) }, { recordIndex := 1077, useUpper := true, coefficient := (-107970994830614960932127471 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1078, useUpper := true, coefficient := (-182649553425640563296709678101 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1079, useUpper := true, coefficient := (-28830908694757487739644630029 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1080, useUpper := true, coefficient := (-1905141752977511462991479 / 12500000000000000000000000000 : Rat) }, { recordIndex := 1081, useUpper := true, coefficient := (-107970994830614960932127471 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1082, useUpper := true, coefficient := (-182649553425640563296709678101 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1083, useUpper := true, coefficient := (-28830908694757487739644630029 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1084, useUpper := false, coefficient := (282968576797833 / 1000000000000000 : Rat) }, { recordIndex := 1085, useUpper := true, coefficient := (-8507064315774488775008139 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1086, useUpper := true, coefficient := (-18665254773569823557528781459 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1087, useUpper := true, coefficient := (-237864846853140943501118315421 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1088, useUpper := true, coefficient := (-7603079111236919608323958881 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1089, useUpper := true, coefficient := (-7603079111236919608323958881 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1090, useUpper := true, coefficient := (-8507064315774488775008139 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1091, useUpper := true, coefficient := (-18665254773569823557528781459 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1092, useUpper := true, coefficient := (-237864846853140943501118315421 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1093, useUpper := false, coefficient := 0 }, { recordIndex := 1094, useUpper := true, coefficient := 0 }, { recordIndex := 1095, useUpper := true, coefficient := 0 }, { recordIndex := 1096, useUpper := true, coefficient := 0 }, { recordIndex := 1097, useUpper := true, coefficient := 0 }, { recordIndex := 1098, useUpper := true, coefficient := 0 }, { recordIndex := 1099, useUpper := false, coefficient := (217031423202167 / 1000000000000000 : Rat) }, { recordIndex := 1100, useUpper := true, coefficient := (-107970994830614960932127471 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1101, useUpper := true, coefficient := (-182649553425640563296709678101 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1102, useUpper := true, coefficient := (-28830908694757487739644630029 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1103, useUpper := true, coefficient := (-1905141752977511462991479 / 12500000000000000000000000000 : Rat) }, { recordIndex := 1104, useUpper := true, coefficient := (-1905141752977511462991479 / 12500000000000000000000000000 : Rat) }, { recordIndex := 1105, useUpper := true, coefficient := (-107970994830614960932127471 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1106, useUpper := true, coefficient := (-182649553425640563296709678101 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1107, useUpper := true, coefficient := (-28830908694757487739644630029 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1108, useUpper := false, coefficient := (282968576797833 / 1000000000000000 : Rat) }, { recordIndex := 1109, useUpper := true, coefficient := (-8507064315774488775008139 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1110, useUpper := true, coefficient := (-7603079111236919608323958881 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1111, useUpper := true, coefficient := (-18665254773569823557528781459 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1112, useUpper := true, coefficient := (-237864846853140943501118315421 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1113, useUpper := true, coefficient := (-7603079111236919608323958881 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1114, useUpper := true, coefficient := (-8507064315774488775008139 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1115, useUpper := true, coefficient := (-18665254773569823557528781459 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1116, useUpper := true, coefficient := (-237864846853140943501118315421 / 1000000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (669852329377 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1126, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1127, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1128, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (155980324831 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1129, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1130, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1131, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (37936031389 / 125000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1132, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1133, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1134, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (116651180709 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1135, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1136, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1137, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1138, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1139, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1140, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (52167101051 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1141, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1142, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1143, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1144, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1145, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1146, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1147, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1148, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1149, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (348740049177 / 500000000000 : Rat)
    constant := (-75335400316504732676851319735129346455661497 / 62500000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1198, useUpper := false, coefficient := (27098770537177 / 125000000000000 : Rat) }, { recordIndex := 1199, useUpper := false, coefficient := (27098770537177 / 125000000000000 : Rat) }, { recordIndex := 1200, useUpper := false, coefficient := (27098770537177 / 62500000000000 : Rat) }, { recordIndex := 1201, useUpper := false, coefficient := (283209820799693 / 1000000000000000 : Rat) }, { recordIndex := 1202, useUpper := false, coefficient := (283209820799693 / 1000000000000000 : Rat) }, { recordIndex := 1203, useUpper := false, coefficient := (283209820799693 / 500000000000000 : Rat) }, { recordIndex := 1204, useUpper := false, coefficient := (14902891 / 1000000000000000 : Rat) }, { recordIndex := 1205, useUpper := false, coefficient := (14902891 / 1000000000000000 : Rat) }, { recordIndex := 1206, useUpper := false, coefficient := (14902891 / 500000000000000 : Rat) }]
  },
  {
    retainedFloor := (348740049177 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1150, useUpper := false, coefficient := (27098770537177 / 125000000000000 : Rat) }, { recordIndex := 1151, useUpper := true, coefficient := (-764014286830428370302453 / 5000000000000000000000000000 : Rat) }, { recordIndex := 1152, useUpper := true, coefficient := (-331351449389090711339164019 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1153, useUpper := true, coefficient := (-4561629805251043529649871641 / 25000000000000000000000000000 : Rat) }, { recordIndex := 1154, useUpper := true, coefficient := (-225551140935802513738422027 / 7812500000000000000000000000 : Rat) }, { recordIndex := 1155, useUpper := true, coefficient := (-764014286830428370302453 / 5000000000000000000000000000 : Rat) }, { recordIndex := 1156, useUpper := true, coefficient := (-331351449389090711339164019 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1157, useUpper := true, coefficient := (-4561629805251043529649871641 / 25000000000000000000000000000 : Rat) }, { recordIndex := 1158, useUpper := true, coefficient := (-225551140935802513738422027 / 7812500000000000000000000000 : Rat) }, { recordIndex := 1159, useUpper := false, coefficient := (283209820799693 / 1000000000000000 : Rat) }, { recordIndex := 1160, useUpper := true, coefficient := (-34267751767855797731620261 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1161, useUpper := true, coefficient := (-37562677851939853104244009587 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1162, useUpper := true, coefficient := (-238013640273774052722633658813 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1163, useUpper := true, coefficient := (-1492432783027963036892846059 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1164, useUpper := true, coefficient := (-1492432783027963036892846059 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1165, useUpper := true, coefficient := (-34267751767855797731620261 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1166, useUpper := true, coefficient := (-37562677851939853104244009587 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1167, useUpper := true, coefficient := (-238013640273774052722633658813 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1168, useUpper := false, coefficient := (14902891 / 1000000000000000 : Rat) }, { recordIndex := 1169, useUpper := true, coefficient := (-2741453156770011156007 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1170, useUpper := true, coefficient := (-2714426021612147071689 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1171, useUpper := true, coefficient := (-2714426021612147071689 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1172, useUpper := true, coefficient := (-12188464978387852928311 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1173, useUpper := true, coefficient := (-590438238851115110769 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1174, useUpper := false, coefficient := (27098770537177 / 125000000000000 : Rat) }, { recordIndex := 1175, useUpper := true, coefficient := (-331351449389090711339164019 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1176, useUpper := true, coefficient := (-4561629805251043529649871641 / 25000000000000000000000000000 : Rat) }, { recordIndex := 1177, useUpper := true, coefficient := (-225551140935802513738422027 / 7812500000000000000000000000 : Rat) }, { recordIndex := 1178, useUpper := true, coefficient := (-764014286830428370302453 / 5000000000000000000000000000 : Rat) }, { recordIndex := 1179, useUpper := true, coefficient := (-764014286830428370302453 / 5000000000000000000000000000 : Rat) }, { recordIndex := 1180, useUpper := true, coefficient := (-331351449389090711339164019 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1181, useUpper := true, coefficient := (-4561629805251043529649871641 / 25000000000000000000000000000 : Rat) }, { recordIndex := 1182, useUpper := true, coefficient := (-225551140935802513738422027 / 7812500000000000000000000000 : Rat) }, { recordIndex := 1183, useUpper := false, coefficient := (283209820799693 / 1000000000000000 : Rat) }, { recordIndex := 1184, useUpper := true, coefficient := (-34267751767855797731620261 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1185, useUpper := true, coefficient := (-1492432783027963036892846059 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1186, useUpper := true, coefficient := (-37562677851939853104244009587 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1187, useUpper := true, coefficient := (-238013640273774052722633658813 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1188, useUpper := true, coefficient := (-1492432783027963036892846059 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1189, useUpper := true, coefficient := (-34267751767855797731620261 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1190, useUpper := true, coefficient := (-37562677851939853104244009587 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1191, useUpper := true, coefficient := (-238013640273774052722633658813 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1192, useUpper := false, coefficient := (14902891 / 1000000000000000 : Rat) }, { recordIndex := 1193, useUpper := true, coefficient := (-2714426021612147071689 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1194, useUpper := true, coefficient := (-2741453156770011156007 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1195, useUpper := true, coefficient := (-2714426021612147071689 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1196, useUpper := true, coefficient := (-12188464978387852928311 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1197, useUpper := true, coefficient := (-590438238851115110769 / 62500000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (335438595049 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1207, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1208, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1209, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (60593867627 / 125000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1210, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1211, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1212, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1213, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1214, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1215, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (281749755747 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1216, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1217, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1218, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1219, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1220, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1221, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1222, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1223, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1224, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (796986227201 / 1000000000000 : Rat)
    constant := (-87644718081564753675308849210562531102017207 / 62500000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1275, useUpper := false, coefficient := (159745191760353 / 500000000000000 : Rat) }, { recordIndex := 1276, useUpper := false, coefficient := (159745191760353 / 500000000000000 : Rat) }, { recordIndex := 1277, useUpper := false, coefficient := (159745191760353 / 250000000000000 : Rat) }, { recordIndex := 1278, useUpper := false, coefficient := (361019226345451 / 2000000000000000 : Rat) }, { recordIndex := 1279, useUpper := false, coefficient := (361019226345451 / 2000000000000000 : Rat) }, { recordIndex := 1280, useUpper := false, coefficient := (361019226345451 / 1000000000000000 : Rat) }, { recordIndex := 1281, useUpper := false, coefficient := (6613137 / 2000000000000000 : Rat) }, { recordIndex := 1282, useUpper := false, coefficient := (6613137 / 2000000000000000 : Rat) }, { recordIndex := 1283, useUpper := false, coefficient := (6613137 / 1000000000000000 : Rat) }]
  },
  {
    retainedFloor := (796986227201 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1225, useUpper := false, coefficient := (159745191760353 / 500000000000000 : Rat) }, { recordIndex := 1226, useUpper := true, coefficient := (-107108691107727199999497801 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1227, useUpper := true, coefficient := (-22734659743185496915012129827 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1228, useUpper := true, coefficient := (-13038367615940922517321242741 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1229, useUpper := true, coefficient := (-107108691107727199999497801 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1230, useUpper := true, coefficient := (-2310823682876698704268027581 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1231, useUpper := true, coefficient := (-190696614378714687869278382607 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1232, useUpper := true, coefficient := (-12301272585546473776676429871 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1233, useUpper := false, coefficient := (361019226345451 / 2000000000000000 : Rat) }, { recordIndex := 1234, useUpper := true, coefficient := (-245522378058871503027831541 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1235, useUpper := true, coefficient := (-29323934255314002729088458113 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1236, useUpper := true, coefficient := (-25690501518897439954875649467 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1237, useUpper := true, coefficient := (-29356614086427155218353217151 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1238, useUpper := true, coefficient := (-25690501518897439954875649467 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1239, useUpper := true, coefficient := (-245522378058871503027831541 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1240, useUpper := true, coefficient := (-57305222989981599558048511 / 1953125000000000000000000000 : Rat) }, { recordIndex := 1241, useUpper := true, coefficient := (-199331149550061210730027895327 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1242, useUpper := false, coefficient := (6613137 / 2000000000000000 : Rat) }, { recordIndex := 1243, useUpper := true, coefficient := (-598807907288388308727 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1244, useUpper := true, coefficient := (-721333151677272064131 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1245, useUpper := true, coefficient := (-7468236794212103421 / 8000000000000000000000000000 : Rat) }, { recordIndex := 1246, useUpper := true, coefficient := (-7468236794212103421 / 8000000000000000000000000000 : Rat) }, { recordIndex := 1247, useUpper := true, coefficient := (-528010673328132839163 / 400000000000000000000000000000 : Rat) }, { recordIndex := 1248, useUpper := true, coefficient := (-346172820782259471201 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1249, useUpper := true, coefficient := (-1442437552063887578361 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1250, useUpper := false, coefficient := (159745191760353 / 500000000000000 : Rat) }, { recordIndex := 1251, useUpper := true, coefficient := (-22734659743185496915012129827 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1252, useUpper := true, coefficient := (-13038367615940922517321242741 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1253, useUpper := true, coefficient := (-107108691107727199999497801 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1254, useUpper := true, coefficient := (-107108691107727199999497801 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1255, useUpper := true, coefficient := (-2310823682876698704268027581 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1256, useUpper := true, coefficient := (-190696614378714687869278382607 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1257, useUpper := true, coefficient := (-12301272585546473776676429871 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1258, useUpper := false, coefficient := (361019226345451 / 2000000000000000 : Rat) }, { recordIndex := 1259, useUpper := true, coefficient := (-245522378058871503027831541 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1260, useUpper := true, coefficient := (-29356614086427155218353217151 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1261, useUpper := true, coefficient := (-25690501518897439954875649467 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1262, useUpper := true, coefficient := (-29323934255314002729088458113 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1263, useUpper := true, coefficient := (-25690501518897439954875649467 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1264, useUpper := true, coefficient := (-245522378058871503027831541 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1265, useUpper := true, coefficient := (-57305222989981599558048511 / 1953125000000000000000000000 : Rat) }, { recordIndex := 1266, useUpper := true, coefficient := (-199331149550061210730027895327 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1267, useUpper := false, coefficient := (6613137 / 2000000000000000 : Rat) }, { recordIndex := 1268, useUpper := true, coefficient := (-7468236794212103421 / 8000000000000000000000000000 : Rat) }, { recordIndex := 1269, useUpper := true, coefficient := (-598807907288388308727 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1270, useUpper := true, coefficient := (-721333151677272064131 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1271, useUpper := true, coefficient := (-7468236794212103421 / 8000000000000000000000000000 : Rat) }, { recordIndex := 1272, useUpper := true, coefficient := (-528010673328132839163 / 400000000000000000000000000000 : Rat) }, { recordIndex := 1273, useUpper := true, coefficient := (-346172820782259471201 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1274, useUpper := true, coefficient := (-1442437552063887578361 / 2000000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (260814109713 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1284, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1285, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1286, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (466595114001 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1287, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1288, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1289, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1290, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1291, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1292, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (151745747511 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1293, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1294, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1295, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1296, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1297, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1298, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1299, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1300, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1301, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (139596197713 / 200000000000 : Rat)
    constant := (-1205995259080065393052601930926118194186310253 / 1000000000000001000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1350, useUpper := false, coefficient := 0 }, { recordIndex := 1351, useUpper := false, coefficient := 0 }, { recordIndex := 1352, useUpper := false, coefficient := 0 }, { recordIndex := 1353, useUpper := false, coefficient := (282971802184935 / 1000000000000001 : Rat) }, { recordIndex := 1354, useUpper := false, coefficient := (282971802184935 / 1000000000000001 : Rat) }, { recordIndex := 1355, useUpper := false, coefficient := (565943604369870 / 1000000000000001 : Rat) }, { recordIndex := 1356, useUpper := false, coefficient := (434056395630131 / 2000000000000002 : Rat) }, { recordIndex := 1357, useUpper := false, coefficient := (434056395630131 / 2000000000000002 : Rat) }, { recordIndex := 1358, useUpper := false, coefficient := (434056395630131 / 1000000000000001 : Rat) }]
  },
  {
    retainedFloor := (139596197713 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1302, useUpper := false, coefficient := 0 }, { recordIndex := 1303, useUpper := true, coefficient := 0 }, { recordIndex := 1304, useUpper := true, coefficient := 0 }, { recordIndex := 1305, useUpper := true, coefficient := 0 }, { recordIndex := 1306, useUpper := true, coefficient := 0 }, { recordIndex := 1307, useUpper := true, coefficient := 0 }, { recordIndex := 1308, useUpper := false, coefficient := (282971802184935 / 1000000000000001 : Rat) }, { recordIndex := 1309, useUpper := true, coefficient := (-2617913437021148398542849 / 15384615384615400000000000000 : Rat) }, { recordIndex := 1310, useUpper := true, coefficient := (-8355132261713464048947537 / 1098901098901100000000000000 : Rat) }, { recordIndex := 1311, useUpper := true, coefficient := (-7466172868810509732966399981 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1312, useUpper := true, coefficient := (-2973345038866460305059005703 / 12500000000000012500000000000 : Rat) }, { recordIndex := 1313, useUpper := true, coefficient := (-8355132261713464048947537 / 1098901098901100000000000000 : Rat) }, { recordIndex := 1314, useUpper := true, coefficient := (-2617913437021148398542849 / 15384615384615400000000000000 : Rat) }, { recordIndex := 1315, useUpper := true, coefficient := (-7466172868810509732966399981 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1316, useUpper := true, coefficient := (-2973345038866460305059005703 / 12500000000000012500000000000 : Rat) }, { recordIndex := 1317, useUpper := false, coefficient := (434056395630131 / 2000000000000002 : Rat) }, { recordIndex := 1318, useUpper := true, coefficient := (-1079686742576731475797152207 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1319, useUpper := true, coefficient := (-365293781666883765167301753081 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 1320, useUpper := true, coefficient := (-403223158183173828642680329 / 13986013986014000000000000000 : Rat) }, { recordIndex := 1321, useUpper := true, coefficient := (-152417458643031289411718901 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 1322, useUpper := true, coefficient := (-152417458643031289411718901 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 1323, useUpper := true, coefficient := (-1079686742576731475797152207 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1324, useUpper := true, coefficient := (-365293781666883765167301753081 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 1325, useUpper := true, coefficient := (-403223158183173828642680329 / 13986013986014000000000000000 : Rat) }, { recordIndex := 1326, useUpper := false, coefficient := 0 }, { recordIndex := 1327, useUpper := true, coefficient := 0 }, { recordIndex := 1328, useUpper := true, coefficient := 0 }, { recordIndex := 1329, useUpper := true, coefficient := 0 }, { recordIndex := 1330, useUpper := true, coefficient := 0 }, { recordIndex := 1331, useUpper := true, coefficient := 0 }, { recordIndex := 1332, useUpper := false, coefficient := (282971802184935 / 1000000000000001 : Rat) }, { recordIndex := 1333, useUpper := true, coefficient := (-2617913437021148398542849 / 15384615384615400000000000000 : Rat) }, { recordIndex := 1334, useUpper := true, coefficient := (-7466172868810509732966399981 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1335, useUpper := true, coefficient := (-2973345038866460305059005703 / 12500000000000012500000000000 : Rat) }, { recordIndex := 1336, useUpper := true, coefficient := (-8355132261713464048947537 / 1098901098901100000000000000 : Rat) }, { recordIndex := 1337, useUpper := true, coefficient := (-8355132261713464048947537 / 1098901098901100000000000000 : Rat) }, { recordIndex := 1338, useUpper := true, coefficient := (-2617913437021148398542849 / 15384615384615400000000000000 : Rat) }, { recordIndex := 1339, useUpper := true, coefficient := (-7466172868810509732966399981 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1340, useUpper := true, coefficient := (-2973345038866460305059005703 / 12500000000000012500000000000 : Rat) }, { recordIndex := 1341, useUpper := false, coefficient := (434056395630131 / 2000000000000002 : Rat) }, { recordIndex := 1342, useUpper := true, coefficient := (-152417458643031289411718901 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 1343, useUpper := true, coefficient := (-1079686742576731475797152207 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1344, useUpper := true, coefficient := (-365293781666883765167301753081 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 1345, useUpper := true, coefficient := (-403223158183173828642680329 / 13986013986014000000000000000 : Rat) }, { recordIndex := 1346, useUpper := true, coefficient := (-152417458643031289411718901 / 1000000000000001000000000000000 : Rat) }, { recordIndex := 1347, useUpper := true, coefficient := (-1079686742576731475797152207 / 200000000000000200000000000000 : Rat) }, { recordIndex := 1348, useUpper := true, coefficient := (-365293781666883765167301753081 / 2000000000000002000000000000000 : Rat) }, { recordIndex := 1349, useUpper := true, coefficient := (-403223158183173828642680329 / 13986013986014000000000000000 : Rat) }]
  },
  {
    retainedFloor := (135490470153 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1359, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1360, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1361, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (690376191909 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1362, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1363, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1364, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (827820042091 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1365, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1366, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1367, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (231191789131 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1368, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1369, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1370, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1371, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1372, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1373, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (252364585549 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1374, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1375, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1376, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1377, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1378, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1379, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1380, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1381, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1382, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (1975635543 / 2500000000 : Rat)
    constant := (-1409592879315936768897865237303382073183752189 / 1000000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1421, useUpper := false, coefficient := (446751606436301 / 2000000000000000 : Rat) }, { recordIndex := 1422, useUpper := false, coefficient := (446751606436301 / 2000000000000000 : Rat) }, { recordIndex := 1423, useUpper := false, coefficient := (446751606436301 / 1000000000000000 : Rat) }, { recordIndex := 1424, useUpper := false, coefficient := (113865097 / 2000000000000000 : Rat) }, { recordIndex := 1425, useUpper := false, coefficient := (113865097 / 2000000000000000 : Rat) }, { recordIndex := 1426, useUpper := false, coefficient := (113865097 / 1000000000000000 : Rat) }, { recordIndex := 1427, useUpper := false, coefficient := (276624139849301 / 1000000000000000 : Rat) }, { recordIndex := 1428, useUpper := false, coefficient := (276624139849301 / 1000000000000000 : Rat) }, { recordIndex := 1429, useUpper := false, coefficient := (276624139849301 / 500000000000000 : Rat) }]
  },
  {
    retainedFloor := (1975635543 / 2500000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1383, useUpper := false, coefficient := (446751606436301 / 2000000000000000 : Rat) }, { recordIndex := 1384, useUpper := true, coefficient := (-3923184725548779016680123939 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1385, useUpper := true, coefficient := (-70902610280116146927595550159 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1386, useUpper := true, coefficient := (-1553444073471312905603210451 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1387, useUpper := true, coefficient := (-3923184725548779016680123939 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1388, useUpper := true, coefficient := (-70902610280116146927595550159 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1389, useUpper := true, coefficient := (-1553444073471312905603210451 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1390, useUpper := false, coefficient := (113865097 / 2000000000000000 : Rat) }, { recordIndex := 1391, useUpper := true, coefficient := (-4431486386044293516973 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1392, useUpper := true, coefficient := (-39529404087159528116589 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1393, useUpper := true, coefficient := (-30020829052397536713681 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1394, useUpper := true, coefficient := (-30020829052397536713681 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1395, useUpper := true, coefficient := (-4431486386044293516973 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1396, useUpper := true, coefficient := (-39529404087159528116589 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1397, useUpper := false, coefficient := (276624139849301 / 1000000000000000 : Rat) }, { recordIndex := 1398, useUpper := true, coefficient := (-24227872207575056434082339213 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1399, useUpper := true, coefficient := (-4021455684929641377940878047 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1400, useUpper := true, coefficient := (-272602684164371358622059121953 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1401, useUpper := true, coefficient := (-44928162754750193565917660787 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1402, useUpper := false, coefficient := (446751606436301 / 2000000000000000 : Rat) }, { recordIndex := 1403, useUpper := true, coefficient := (-3923184725548779016680123939 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1404, useUpper := true, coefficient := (-70902610280116146927595550159 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1405, useUpper := true, coefficient := (-1553444073471312905603210451 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1406, useUpper := true, coefficient := (-3923184725548779016680123939 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1407, useUpper := true, coefficient := (-70902610280116146927595550159 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1408, useUpper := true, coefficient := (-1553444073471312905603210451 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1409, useUpper := false, coefficient := (113865097 / 2000000000000000 : Rat) }, { recordIndex := 1410, useUpper := true, coefficient := (-4431486386044293516973 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1411, useUpper := true, coefficient := (-30020829052397536713681 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1412, useUpper := true, coefficient := (-39529404087159528116589 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1413, useUpper := true, coefficient := (-30020829052397536713681 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1414, useUpper := true, coefficient := (-4431486386044293516973 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1415, useUpper := true, coefficient := (-39529404087159528116589 / 2000000000000000000000000000000 : Rat) }, { recordIndex := 1416, useUpper := false, coefficient := (276624139849301 / 1000000000000000 : Rat) }, { recordIndex := 1417, useUpper := true, coefficient := (-24227872207575056434082339213 / 250000000000000000000000000000 : Rat) }, { recordIndex := 1418, useUpper := true, coefficient := (-4021455684929641377940878047 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1419, useUpper := true, coefficient := (-272602684164371358622059121953 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1420, useUpper := true, coefficient := (-44928162754750193565917660787 / 250000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (63094047903 / 250000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1430, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1431, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1432, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (231169329307 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1433, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1434, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1435, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1436, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1437, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1438, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (434305057859 / 500000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1439, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1440, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1441, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1442, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1443, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1444, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (49870190751 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1445, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1446, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1447, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (790288412733 / 1000000000000 : Rat)
    constant := (-1409657974480893947450439238629365765829567087 / 1000000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1486, useUpper := false, coefficient := (553308309396683 / 2000000000000000 : Rat) }, { recordIndex := 1487, useUpper := false, coefficient := (553308309396683 / 2000000000000000 : Rat) }, { recordIndex := 1488, useUpper := false, coefficient := (553308309396683 / 1000000000000000 : Rat) }, { recordIndex := 1489, useUpper := false, coefficient := (73 / 2000000000000000 : Rat) }, { recordIndex := 1490, useUpper := false, coefficient := (73 / 2000000000000000 : Rat) }, { recordIndex := 1491, useUpper := false, coefficient := (73 / 1000000000000000 : Rat) }, { recordIndex := 1492, useUpper := false, coefficient := (111672922650811 / 500000000000000 : Rat) }, { recordIndex := 1493, useUpper := false, coefficient := (111672922650811 / 500000000000000 : Rat) }, { recordIndex := 1494, useUpper := false, coefficient := (111672922650811 / 250000000000000 : Rat) }]
  },
  {
    retainedFloor := (790288412733 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1448, useUpper := false, coefficient := (553308309396683 / 2000000000000000 : Rat) }, { recordIndex := 1449, useUpper := true, coefficient := (-48461210024730600692333888593 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1450, useUpper := true, coefficient := (-200945855016222130846957639 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1451, useUpper := true, coefficient := (-13631761879900852869153042361 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1452, useUpper := true, coefficient := (-89865867324440149307666111407 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1453, useUpper := false, coefficient := (73 / 2000000000000000 : Rat) }, { recordIndex := 1454, useUpper := true, coefficient := (-11885927575168301 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1455, useUpper := true, coefficient := (-12307166102469213 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1456, useUpper := true, coefficient := (-6153453161181243 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1457, useUpper := true, coefficient := (-12307166102469213 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1458, useUpper := true, coefficient := (-11885927575168301 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1459, useUpper := true, coefficient := (-6153453161181243 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1460, useUpper := false, coefficient := (111672922650811 / 500000000000000 : Rat) }, { recordIndex := 1461, useUpper := true, coefficient := (-4903809139383296179661805349 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1462, useUpper := true, coefficient := (-70884120590073860804261769317 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1463, useUpper := true, coefficient := (-1558328945670769758443787891 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1464, useUpper := true, coefficient := (-4903809139383296179661805349 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1465, useUpper := true, coefficient := (-70884120590073860804261769317 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1466, useUpper := true, coefficient := (-1558328945670769758443787891 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1467, useUpper := false, coefficient := (553308309396683 / 2000000000000000 : Rat) }, { recordIndex := 1468, useUpper := true, coefficient := (-48461210024730600692333888593 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1469, useUpper := true, coefficient := (-200945855016222130846957639 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1470, useUpper := true, coefficient := (-13631761879900852869153042361 / 50000000000000000000000000000 : Rat) }, { recordIndex := 1471, useUpper := true, coefficient := (-89865867324440149307666111407 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1472, useUpper := false, coefficient := (73 / 2000000000000000 : Rat) }, { recordIndex := 1473, useUpper := true, coefficient := (-11885927575168301 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1474, useUpper := true, coefficient := (-6153453161181243 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1475, useUpper := true, coefficient := (-12307166102469213 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1476, useUpper := true, coefficient := (-12307166102469213 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1477, useUpper := true, coefficient := (-11885927575168301 / 1000000000000000000000000000000 : Rat) }, { recordIndex := 1478, useUpper := true, coefficient := (-6153453161181243 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1479, useUpper := false, coefficient := (111672922650811 / 500000000000000 : Rat) }, { recordIndex := 1480, useUpper := true, coefficient := (-4903809139383296179661805349 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1481, useUpper := true, coefficient := (-70884120590073860804261769317 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1482, useUpper := true, coefficient := (-1558328945670769758443787891 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1483, useUpper := true, coefficient := (-4903809139383296179661805349 / 62500000000000000000000000000 : Rat) }, { recordIndex := 1484, useUpper := true, coefficient := (-70884120590073860804261769317 / 500000000000000000000000000000 : Rat) }, { recordIndex := 1485, useUpper := true, coefficient := (-1558328945670769758443787891 / 500000000000000000000000000000 : Rat) }]
  },
  {
    retainedFloor := (669852329377 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1495, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1496, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1497, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (138388593277 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1498, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1499, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1500, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (106125052313 / 200000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1501, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1502, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1503, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530043551259 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1504, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1505, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1506, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (530044741261 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1507, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1508, useUpper := false, coefficient := (1 / 3 : Rat) }, { recordIndex := 1509, useUpper := false, coefficient := (1 / 3 : Rat) }]
  },
  {
    retainedFloor := (699779321439 / 1000000000000 : Rat)
    constant := (-124147997442788489531377035599909775970520367 / 100000000000000000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1540, useUpper := false, coefficient := (66666293490431 / 200000000000000 : Rat) }, { recordIndex := 1541, useUpper := false, coefficient := (66666293490431 / 200000000000000 : Rat) }, { recordIndex := 1542, useUpper := false, coefficient := (66666293490431 / 100000000000000 : Rat) }, { recordIndex := 1543, useUpper := false, coefficient := (33333706509569 / 200000000000000 : Rat) }, { recordIndex := 1544, useUpper := false, coefficient := (33333706509569 / 200000000000000 : Rat) }, { recordIndex := 1545, useUpper := false, coefficient := (33333706509569 / 100000000000000 : Rat) }, { recordIndex := 1546, useUpper := false, coefficient := 0 }, { recordIndex := 1547, useUpper := false, coefficient := 0 }, { recordIndex := 1548, useUpper := false, coefficient := 0 }]
  },
  {
    retainedFloor := (699779321439 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1510, useUpper := false, coefficient := (66666293490431 / 200000000000000 : Rat) }, { recordIndex := 1511, useUpper := true, coefficient := (-50824370199625478217919796849 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1512, useUpper := true, coefficient := (-15841923290805521782080203151 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1513, useUpper := true, coefficient := (-50824370199625478217919796849 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1514, useUpper := true, coefficient := (-15841923290805521782080203151 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1515, useUpper := false, coefficient := (33333706509569 / 200000000000000 : Rat) }, { recordIndex := 1516, useUpper := true, coefficient := (-792108857305470805837633209 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1517, useUpper := true, coefficient := (-2541261793651429194162366791 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1518, useUpper := true, coefficient := (-2541261793651429194162366791 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1519, useUpper := true, coefficient := (-792108857305470805837633209 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1520, useUpper := false, coefficient := 0 }, { recordIndex := 1521, useUpper := true, coefficient := 0 }, { recordIndex := 1522, useUpper := true, coefficient := 0 }, { recordIndex := 1523, useUpper := true, coefficient := 0 }, { recordIndex := 1524, useUpper := true, coefficient := 0 }, { recordIndex := 1525, useUpper := false, coefficient := (66666293490431 / 200000000000000 : Rat) }, { recordIndex := 1526, useUpper := true, coefficient := (-50824370199625478217919796849 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1527, useUpper := true, coefficient := (-15841923290805521782080203151 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1528, useUpper := true, coefficient := (-50824370199625478217919796849 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1529, useUpper := true, coefficient := (-15841923290805521782080203151 / 200000000000000000000000000000 : Rat) }, { recordIndex := 1530, useUpper := false, coefficient := (33333706509569 / 200000000000000 : Rat) }, { recordIndex := 1531, useUpper := true, coefficient := (-792108857305470805837633209 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1532, useUpper := true, coefficient := (-2541261793651429194162366791 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1533, useUpper := true, coefficient := (-2541261793651429194162366791 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1534, useUpper := true, coefficient := (-792108857305470805837633209 / 20000000000000000000000000000 : Rat) }, { recordIndex := 1535, useUpper := false, coefficient := 0 }, { recordIndex := 1536, useUpper := true, coefficient := 0 }, { recordIndex := 1537, useUpper := true, coefficient := 0 }, { recordIndex := 1538, useUpper := true, coefficient := 0 }, { recordIndex := 1539, useUpper := true, coefficient := 0 }]
  },
  {
    retainedFloor := (704380756951 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1549, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1550, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1551, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1552, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1553, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1554, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (548031450587 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1555, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1556, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1557, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := 0
    constant := 0
    terms := [{ recordIndex := 1558, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1559, useUpper := false, coefficient := (790643 / 2000000 : Rat) }, { recordIndex := 1560, useUpper := false, coefficient := (790643 / 2000000 : Rat) }]
  },
  {
    retainedFloor := (1490513549769 / 1000000000000 : Rat)
    constant := (-2830114015881672025944380699373 / 1000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1561, useUpper := false, coefficient := 1 }, { recordIndex := 1563, useUpper := false, coefficient := 1 }]
  },
  {
    retainedFloor := (1490513549769 / 1000000000000 : Rat)
    constant := (-2830114015881672025944380699373 / 1000000000000000000000000000000 : Rat)
    terms := [{ recordIndex := 1562, useUpper := false, coefficient := 1 }, { recordIndex := 1563, useUpper := false, coefficient := 1 }]
  },
  {
    retainedFloor := (1490513549769 / 1000000000000 : Rat)
    constant := 0
    terms := [{ recordIndex := 1564, useUpper := false, coefficient := 1 }, { recordIndex := 1565, useUpper := true, coefficient := (-145624853 / 1000000000000000 : Rat) }, { recordIndex := 1566, useUpper := true, coefficient := (-3235519461 / 200000000000000 : Rat) }, { recordIndex := 1567, useUpper := true, coefficient := (-1012519317451 / 2000000000000000 : Rat) }, { recordIndex := 1568, useUpper := true, coefficient := (-1899636723147 / 400000000000000 : Rat) }, { recordIndex := 1569, useUpper := true, coefficient := (-12938280255711 / 1000000000000000 : Rat) }, { recordIndex := 1570, useUpper := true, coefficient := (-9673606557771 / 2000000000000000 : Rat) }, { recordIndex := 1571, useUpper := true, coefficient := (-1009879300421 / 2000000000000000 : Rat) }, { recordIndex := 1572, useUpper := true, coefficient := (-33412921251 / 2000000000000000 : Rat) }, { recordIndex := 1573, useUpper := true, coefficient := (-302564579 / 2000000000000000 : Rat) }, { recordIndex := 1574, useUpper := true, coefficient := (-3235519461 / 200000000000000 : Rat) }, { recordIndex := 1575, useUpper := true, coefficient := (-1012519317451 / 2000000000000000 : Rat) }, { recordIndex := 1576, useUpper := true, coefficient := (-1899636723147 / 400000000000000 : Rat) }, { recordIndex := 1577, useUpper := true, coefficient := (-12938280255711 / 1000000000000000 : Rat) }, { recordIndex := 1578, useUpper := true, coefficient := (-9673606557771 / 2000000000000000 : Rat) }, { recordIndex := 1579, useUpper := true, coefficient := (-1009879300421 / 2000000000000000 : Rat) }, { recordIndex := 1580, useUpper := true, coefficient := (-33412921251 / 2000000000000000 : Rat) }, { recordIndex := 1581, useUpper := true, coefficient := (-302564579 / 2000000000000000 : Rat) }, { recordIndex := 1582, useUpper := true, coefficient := (-23456281619827 / 1000000000000000 : Rat) }, { recordIndex := 1583, useUpper := true, coefficient := (-113194166373899 / 1000000000000000 : Rat) }, { recordIndex := 1584, useUpper := true, coefficient := (-288356290392193 / 1000000000000000 : Rat) }, { recordIndex := 1585, useUpper := true, coefficient := (-171793579140753 / 500000000000000 : Rat) }, { recordIndex := 1586, useUpper := true, coefficient := (-41228146839217 / 250000000000000 : Rat) }, { recordIndex := 1587, useUpper := true, coefficient := (-9392365056437 / 500000000000000 : Rat) }, { recordIndex := 1588, useUpper := true, coefficient := (-28591012737 / 50000000000000 : Rat) }]
  },
]

def entropyEndpoint (useUpper : Bool) : List Nat -> Option Rat
  | [] => some 0
  | logIndex :: tail => do
      let entry <- MME.DWZFourthLogScaleTable.entries[logIndex]?
      let rest <- entropyEndpoint useUpper tail
      let logBound := if useUpper then
        MME.autoScaledLogLower entry.1 entry.2 6
      else
        MME.autoScaledLogUpper entry.1 entry.2 6
      pure (-(entry.1 * logBound) + rest)

def recordAccepts (record : EntropyRecord) : Bool :=
  match entropyEndpoint false record.cells,
      entropyEndpoint true record.cells with
  | some lower, some upper =>
      decide (record.lowerFloor <= lower /\ upper <= record.upperCeiling)
  | _, _ => false

def termSafe (term : EntropyTerm) : Bool :=
  if term.useUpper then decide (term.coefficient <= 0)
  else decide (0 <= term.coefficient)

def termValue (term : EntropyTerm) : Option Rat := do
  let record <- entropyRecords[term.recordIndex]?
  let endpoint := if term.useUpper then record.upperCeiling
    else record.lowerFloor
  pure (term.coefficient * endpoint)

def termsValue : List EntropyTerm -> Option Rat
  | [] => some 0
  | term :: tail => do
      let value <- termValue term
      let rest <- termsValue tail
      pure (value + rest)

def branchAccepts (branch : FloorBranch) : Bool :=
  branch.terms.all termSafe &&
    match termsValue branch.terms with
    | none => false
    | some value =>
        decide (branch.retainedFloor <= branch.constant + value)

def checkRetainedEntropy : Bool :=
  entropyRecords.all recordAccepts && obligations.all branchAccepts

end MME.DWZFourthRetainedEntropy


